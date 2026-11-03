#![no_std]
//#![cfg_attr(all(feature = "nightly", feature = "simd"), feature(stdsimd))]
#![allow(clippy::inconsistent_digit_grouping)]
#![warn(unsafe_op_in_unsafe_fn)]
#[macro_use]
mod parse;

//use log::*;
// mod parse_i16;
// mod parse_i32;
// mod parse_i8;
// mod parse_u16;
// mod parse_u32;
// mod parse_u8;

use core::num::IntErrorKind;

pub use parse::{parse, parse_challenger, parse_from_str, FromStrRadixHelper};
// pub use parse_i16::{parse_i16, parse_i16_challenger};
// pub use parse_i32::{parse_i32, parse_i32_challenger};
// pub use parse_i8::{parse_i8, parse_i8_challenger};
// pub use parse_u16::{parse_u16, parse_u16_challenger};
// pub use parse_u32::{parse_u32, parse_u32_challenger};
// pub use parse_u8::{parse_u8, parse_u8_challenger};

const PLUS: u8 = b'+'.wrapping_sub(b'0');
const MINUS: u8 = b'-'.wrapping_sub(b'0');

/// A public version of `std::num::ParseIntError`
#[derive(Debug, Eq, PartialEq)]
pub struct ParseIntErrorPublic {
    pub kind: IntErrorKind,
}

type Pie = ParseIntErrorPublic;
// SWAR digit parsing.
//
// Every helper below works on a "chunk": 2, 4 or 8 ASCII bytes loaded
// little-endian into an integer (so the first character is the lowest byte)
// and XORed with 0x30 in every byte. For valid digits that leaves each byte
// holding 0..=9. `validN` checks that every byte is 0..=9 and `valueN` folds
// the digits into a number. The value is computed speculatively and validity
// is checked afterwards so the two don't serialise.
//
// Only 8-byte chunks are used for anything longer than 8 digits: u128 SWAR
// is slower than two u64 SWARs on every target we've measured.

/// SAFETY: `p` must be readable for 2 bytes. Alignment doesn't matter.
#[inline(always)]
unsafe fn ld2(p: *const u8) -> u16 {
    u16::from_le_bytes(unsafe { core::ptr::read_unaligned(p as *const [u8; 2]) }) ^ 0x3030
}
/// SAFETY: `p` must be readable for 4 bytes. Alignment doesn't matter.
#[inline(always)]
unsafe fn ld4(p: *const u8) -> u32 {
    u32::from_le_bytes(unsafe { core::ptr::read_unaligned(p as *const [u8; 4]) }) ^ 0x30303030
}
/// SAFETY: `p` must be readable for 8 bytes. Alignment doesn't matter.
#[inline(always)]
unsafe fn ld8(p: *const u8) -> u64 {
    u64::from_le_bytes(unsafe { core::ptr::read_unaligned(p as *const [u8; 8]) })
        ^ 0x3030303030303030
}

// A byte b is a digit iff its high nibble is 0 and b + 0x76 doesn't set the
// high bit (i.e. b <= 9).
#[inline(always)]
fn valid2(c: u16) -> bool {
    (c & 0xf0f0) | (c.wrapping_add(0x7676) & 0x8080) == 0
}
#[inline(always)]
fn valid4(c: u32) -> bool {
    (c & 0xf0f0f0f0) | (c.wrapping_add(0x76767676) & 0x80808080) == 0
}
#[inline(always)]
fn valid8(c: u64) -> bool {
    (c & 0xf0f0f0f0f0f0f0f0) | (c.wrapping_add(0x7676767676767676) & 0x8080808080808080) == 0
}

#[inline(always)]
fn value2(c: u16) -> u16 {
    (c & 0x000f) * 10 + (c >> 8)
}
#[inline(always)]
fn value4(c: u32) -> u16 {
    let c = ((c & 0x0f000f00) >> 8) + (c & 0x000f000f) * 10;
    ((c & 0x00ff) * 100 + (c >> 16)) as u16
}
#[inline(always)]
fn value8(c: u64) -> u32 {
    let c = ((c & 0x0f000f000f000f00) >> 8) + (c & 0x000f000f000f000f) * 10;
    let c = ((c & 0x00ff000000ff0000) >> 16) + (c & 0x000000ff000000ff) * 100;
    ((c & 0xffff) * 10000 + (c >> 32)) as u32
}

#[inline(always)]
fn invalid() -> Pie {
    Pie {
        kind: IntErrorKind::InvalidDigit,
    }
}

/// Parse the first 2 chars in a u8 slice as a base 10 integer.
/// SAFETY: slice length must be at least 2.
#[doc(hidden)]
#[inline]
pub unsafe fn parse_2_chars(s: &[u8]) -> Result<u16, Pie> {
    debug_assert!(s.len() >= 2);
    let c = unsafe { ld2(s.as_ptr()) };
    if likely!(valid2(c)) {
        Ok(value2(c))
    } else {
        Err(invalid())
    }
}

/// Parse the first 4 chars in a u8 slice as a base 10 integer.
/// SAFETY: slice length must be at least 4.
#[doc(hidden)]
#[inline]
pub unsafe fn parse_4_chars(s: &[u8]) -> Result<u16, Pie> {
    debug_assert!(s.len() >= 4);
    let c = unsafe { ld4(s.as_ptr()) };
    if likely!(valid4(c)) {
        Ok(value4(c))
    } else {
        Err(invalid())
    }
}

/// Parse the first 8 chars in a u8 slice as a base 10 integer.
/// SAFETY: slice length must be at least 8.
#[doc(hidden)]
#[inline]
pub unsafe fn parse_8_chars(s: &[u8]) -> Result<u32, Pie> {
    debug_assert!(s.len() >= 8);
    let c = unsafe { ld8(s.as_ptr()) };
    if likely!(valid8(c)) {
        Ok(value8(c))
    } else {
        Err(invalid())
    }
}

/// Parse the first 16 chars in a u8 slice as a base 10 integer.
/// SAFETY: slice length must be at least 16.
#[doc(hidden)]
#[inline]
pub unsafe fn parse_16_chars(s: &[u8]) -> Result<u64, Pie> {
    debug_assert!(s.len() >= 16);
    let (a, b) = unsafe { (ld8(s.as_ptr()), ld8(s.as_ptr().add(8))) };
    if likely!(valid8(a) & valid8(b)) {
        Ok(value8(a) as u64 * 1_0000_0000 + value8(b) as u64)
    } else {
        Err(invalid())
    }
}

/// Parse the first 32 chars in a u8 slice as a base 10 integer.
/// SAFETY: slice length must be at least 32.
#[doc(hidden)]
#[inline]
pub unsafe fn parse_32_chars(s: &[u8]) -> Result<u128, Pie> {
    debug_assert!(s.len() >= 32);
    let p = s.as_ptr();
    let (a, b, c, d) = unsafe { (ld8(p), ld8(p.add(8)), ld8(p.add(16)), ld8(p.add(24))) };
    if likely!(valid8(a) & valid8(b) & valid8(c) & valid8(d)) {
        let hi = value8(a) as u64 * 1_0000_0000 + value8(b) as u64;
        let lo = value8(c) as u64 * 1_0000_0000 + value8(d) as u64;
        Ok(hi as u128 * 1_0000_0000_0000_0000 + lo as u128)
    } else {
        Err(invalid())
    }
}

/// Parse `s` (1..=38 ASCII digits, no sign) as a non-negative number.
///
/// Returns `Err(InvalidDigit)` if any byte is not a digit. Never overflows:
/// callers guarantee `s.len() < T::CHARS`, so the result always fits.
///
/// Lengths that aren't a whole number of chunks are read as overlapping
/// chunks: the trailing chunks exactly, plus a head chunk shifted so that only
/// the leading `len % chunk` digits remain (the vacated low bytes read as
/// `'0'`). That avoids any per-length loop or alignment fix-ups.
#[inline(always)]
pub(crate) fn parse_digits<T: FromStrRadixHelper>(s: &[u8]) -> Result<T, Pie> {
    let l = s.len();
    let p = s.as_ptr();
    debug_assert!(l >= 1 && l < T::CHARS);
    // SAFETY: every caller checks `1 <= l < T::CHARS`.
    unsafe { core::hint::assert_unchecked(l >= 1 && l < T::CHARS) };
    unsafe {
        if l <= 8 {
            if l <= 2 {
                if l == 1 {
                    let d = *p ^ b'0';
                    return if likely!(d <= 9) {
                        Ok(T::from_u8(d))
                    } else {
                        Err(invalid())
                    };
                }
                let c = ld2(p);
                return if likely!(valid2(c)) {
                    Ok(T::from_u16(value2(c)))
                } else {
                    Err(invalid())
                };
            }
            if l <= 4 {
                let hi = ld2(p) << ((4 - l) * 8);
                let lo = ld2(p.add(l - 2));
                return if likely!(valid2(hi) & valid2(lo)) {
                    Ok(T::from_u16(value2(hi) * 100 + value2(lo)))
                } else {
                    Err(invalid())
                };
            }
            let hi = ld4(p) << ((8 - l) * 8);
            let lo = ld4(p.add(l - 4));
            return if likely!(valid4(hi) & valid4(lo)) {
                Ok(T::from_u32(value4(hi) as u32 * 10000 + value4(lo) as u32))
            } else {
                Err(invalid())
            };
        }
        if l <= 16 {
            let hi = ld8(p) << ((16 - l) * 8);
            let lo = ld8(p.add(l - 8));
            return if likely!(valid8(hi) & valid8(lo)) {
                Ok(T::from_u64(
                    value8(hi) as u64 * 1_0000_0000 + value8(lo) as u64,
                ))
            } else {
                Err(invalid())
            };
        }
        // 17..=38 digits (only u64, i64, u128, i128 and 64-bit usize get here).
        // Head holds the leading `l % 8` digits (or 8 if `l % 8 == 0`), then
        // whole 8-digit chunks follow.
        let r = ((l - 1) % 8) + 1;
        let hi = ld8(p) << ((8 - r) * 8);
        let a = ld8(p.add(r));
        let b = ld8(p.add(r + 8));
        let ok = valid8(hi) & valid8(a) & valid8(b);
        let top = value8(hi) as u64 * 1_0000_0000 + value8(a) as u64;
        if T::BITS <= 64 || l <= 24 {
            // 17..=24 digits: top * 10^8 + b. For 64-bit types l <= 19 so
            // this fits a u64.
            return if likely!(ok) {
                if T::BITS <= 64 {
                    Ok(T::from_u64(top * 1_0000_0000 + value8(b) as u64))
                } else {
                    Ok(T::from_u128(top as u128 * 1_0000_0000 + value8(b) as u128))
                }
            } else {
                Err(invalid())
            };
        }
        let c = ld8(p.add(r + 16));
        let ok = ok & valid8(c);
        let bottom = value8(b) as u64 * 1_0000_0000 + value8(c) as u64;
        if l <= 32 {
            return if likely!(ok) {
                Ok(T::from_u128(
                    top as u128 * 1_0000_0000_0000_0000 + bottom as u128,
                ))
            } else {
                Err(invalid())
            };
        }
        let d = ld8(p.add(r + 24));
        if likely!(ok & valid8(d)) {
            let v = (top as u128 * 1_0000_0000_0000_0000 + bottom as u128) * 1_0000_0000
                + value8(d) as u128;
            Ok(T::from_u128(v))
        } else {
            Err(invalid())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::FromStrRadixHelper;
    use heapless::Vec;
    use numtoa::NumToA;
    use paste::paste;

    // #[wasm_bindgen_test]
    // #[test]
    // fn test_uu128_specific() {
    //     let s = "+000123";
    //     let p: Result<u128, ()> = s.parse().map_err(|_| ());
    //     assert_eq!(
    //         p,
    //         super::parse::<u128>(s.as_bytes()).map_err(|_| ()),
    //         "fail to parse: '{}'",
    //         &s
    //     );
    // }

    #[test]
    fn test_bench32() {
        // A way to dbg! in no_std:
        //        env_logger::init();

        let s = "34028236692093846346337460743176821145";
        assert_eq!(
            Ok(34028236692093846346337460743176_u128),
            unsafe { super::parse_32_chars(s.as_bytes()).map_err(|_| ()) },
            "fail to parse: '{}'",
            &s
        );
    }

    #[test]
    fn test_uu12ddd8_specific() {
        //             340282366920938463463374607431768211455
        //let s = "34028236692093846346337460743176821145";
        let s = "01234567890123456789012345678901234567";
        let p: Result<u128, ()> = s.parse().map_err(|_| ());
        //assert_matches!(p, Ok(_));
        assert_eq!(
            p,
            super::parse::<u128>(s.as_bytes()).map_err(|_| ()),
            "fail to parse: '{}'",
            &s
        );
    }

    macro_rules! gen_tests {
        ($target_type:ty, $min:expr, $max:expr, $step: expr, $max_chars: literal,$postfix: literal, $specific: literal) => {
            paste! {
                #[wasm_bindgen_test]
                #[test]
                fn [<test_ $target_type _specific $postfix>]() {
                    let s = $specific;
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_invalid_ascii_ $target_type $postfix>]() {
                    let mut vec = Vec::<_, 42>::new();
                    for &ascii in [b':', b'/'].iter() {
                        for i in 1..$max_chars {
                            vec.clear();
                            for _ in 0..i {
                                vec.push(b'1').unwrap();
                            }
                            for j in 1..i {
                                let mut v = vec.clone();
                                v[j] = ascii;
                                let s = unsafe { core::str::from_utf8_unchecked(&v[..]) };
                                assert_eq!(Err(ParseIntErrorPublic{kind:IntErrorKind::InvalidDigit}), [<parse $postfix>]::<$target_type>(s.as_bytes()), "parsing `{}`", s);
                            }
                        }
                    }
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_invalid_too_big_ $target_type $postfix>]() {
                    let mut s = [0u8; 42];
                    let ss = ($target_type::MAX as $target_type).numtoa(10, &mut s);
                    let len = ss.len();
                    s[len] = b'1';
                    let s = unsafe { core::str::from_utf8_unchecked(&s[..len + 1]) };
                    assert_eq!(
                        Err(()),
                        [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_|()),
                        " when parsing '{}'",
                        &s
                    );
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_empty_ $target_type $postfix>]() {
                    assert_eq!(
                        Err(Pie {
                            kind: IntErrorKind::Empty
                        }),
                        [<parse $postfix>]::<$target_type>("".as_bytes())
                    );
                }

                //#[wasm_bindgen_test] step too small for wasm
                #[cfg_attr(miri, ignore)]
                #[test]
                fn [<test_ $target_type $postfix>]() {
                    let mut s = [0u8; 42];

                    for i in ($min..$max as $target_type).step_by($step) {
                        let s = unsafe { core::str::from_utf8_unchecked(i.numtoa(10, &mut s)) };
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[cfg_attr(miri, ignore)]
                #[test]
                fn [<test_random_ $target_type $postfix>]() {
                    use rand::prelude::*;
                    let mut s = [0u8; 42];
                    let mut rng = rand::rng();

                    for _ in 1..100_000 {
                        let i = rng.random::<$target_type>();
                        let s = unsafe { core::str::from_utf8_unchecked(i.numtoa(10, &mut s)) };
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                //#[wasm_bindgen_test] step too small for wasm
                #[cfg_attr(miri, ignore)]
                #[test]
                fn [<test_ $target_type _plus $postfix>]() {
                    for i in ($min..$max as $target_type).step_by($step) {
                        let mut s = [0u8; 42];
                        s[0] = b'+';
                        let ss = i.numtoa(10, &mut s[1..]);
                        let len = ss.len();
                        let s = unsafe { core::str::from_utf8_unchecked(&s[0..len+1]) };
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_does_not_accept_plus_after_zero_ $target_type _plus $postfix>]() {
                    let mut s = [0u8; 50];
                    s[s.len() - 1] = b'+';
                    let s = unsafe { core::str::from_utf8_unchecked(&s) };
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{:?}'", &s);
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_accepts_many_zeros_ $target_type _plus $postfix>]() {
                    //let i = $max;
                    let s = [0u8; 142];
                    let s = unsafe { core::str::from_utf8_unchecked(&s) };
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }

                #[wasm_bindgen_test]
                #[test]
                fn [<test_accepts_many_leading_zeros_ $target_type _plus $postfix>]() {
                    let mut s = [0u8; 142];
                    let ss = ($target_type::MAX as $target_type).numtoa(10, &mut s[100..]);
                    let len = ss.len();

                    let s = unsafe { core::str::from_utf8_unchecked(&s[..100 + len]) };
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse $postfix>]::<$target_type>(s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }
            }
        }
    }

    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "", "1");
    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "_challenger", "+200");

    gen_tests!(i8, i8::MIN, i8::MAX, 1, 3, "", "1");
    gen_tests!(i8, i8::MIN, i8::MAX, 1, 3, "_challenger", "-99");

    gen_tests!(u16, u16::MIN, u16::MAX, 1, 5, "", "1");
    gen_tests!(u16, u16::MIN, u16::MAX, 1, 5, "_challenger", "1");

    gen_tests!(i16, i16::MIN, i16::MAX, 1, 5, "", "1");
    gen_tests!(i16, i16::MIN, i16::MAX, 1, 5, "_challenger", "1");

    gen_tests!(u32, u32::MIN, u32::MAX, 10_301, 10, "", "1");
    gen_tests!(
        u32,
        u32::MIN,
        u32::MAX,
        10_301,
        10,
        "_challenger",
        "4294967295"
    );

    gen_tests!(i32, i32::MIN, i32::MAX, 10_301, 10, "", "-2147483648");
    gen_tests!(i32, i32::MIN, i32::MAX, 10_301, 10, "_challenger", "1");

    #[cfg(target_pointer_width = "16")]
    const LARGE_STEP: usize = 12345;

    #[cfg(target_pointer_width = "32")]
    const LARGE_STEP: usize = usize::MAX;

    #[cfg(target_pointer_width = "64")]
    const LARGE_STEP: usize = 100_301_000_000_000;

    gen_tests!(
        u64,
        u64::MIN,
        u64::MAX,
        LARGE_STEP,
        20,
        "",
        "0000000000000000018446744073709551615"
    );
    gen_tests!(
        u64,
        u64::MIN,
        u64::MAX,
        LARGE_STEP,
        20,
        "_challenger",
        "10000009700000000000"
    );

    gen_tests!(
        i64,
        i64::MIN,
        i64::MAX,
        LARGE_STEP,
        19,
        "",
        "-999993949854775808"
    );

    gen_tests!(i64, i64::MIN, i64::MAX, LARGE_STEP, 19, "_challenger", "1");

    gen_tests!(
        u128,
        u64::MIN as u128,
        u64::MAX,
        LARGE_STEP,
        39,
        "",
        "10000009700000000000"
    );

    gen_tests!(
        u128,
        u64::MIN as u128,
        u64::MAX,
        LARGE_STEP,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );

    gen_tests!(
        i128,
        u64::MIN as i128,
        u64::MAX,
        LARGE_STEP,
        39,
        "",
        "1701411834604692317316873037158841057271" // "1:11111111111111"
    );

    gen_tests!(
        i128,
        u64::MIN as i128,
        u64::MAX,
        LARGE_STEP,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );

    use wasm_bindgen_test::wasm_bindgen_test;

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz1() {
        // needed checked add when checking digits in range.
        check::<u32, 4>([50, 35, 43, 120]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz2() {
        // Too long is defined by std as invalid digit error rather than overflow.
        check::<u32, 11>([48, 48, 54, 54, 49, 54, 56, 57, 54, 49, 51]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz3() {
        //"00661689613" std can deal with any number of leading zeros
        // as it keeps multiplying them by 10...
        check::<u32, 11>([54, 48, 48, 48, 54, 48, 54, 48, 54, 48, 54]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz4() {
        //leading zeros then plus: "0000+6600660"
        check::<u32, 12>([48, 48, 48, 48, 43, 54, 54, 48, 48, 54, 54, 48]);
    }
    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz5() {
        //leading zeros then plus: "0000+6600660"
        check::<u32, 94>([
            43, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48,
        ]);
    }
    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz6() {
        check::<u64, 21>([
            43, 49, 43, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
        ]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz7() {
        check::<u64, 3>([45, 57, 166]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz8() {
        check::<i8, 6>([45, 48, 48, 48, 48, 176]);
    }

    #[wasm_bindgen_test]
    #[test]
    fn test_fuzz9() {
        check::<u64, 3>([45, 49, 170]);
    }

    fn check<T, const N: usize>(data: [u8; N])
    where
        T: FromStrRadixHelper,
        T: core::str::FromStr,
        T: core::fmt::Debug,
    {
        let mut s = heapless::String::<N>::new();
        for c in &data {
            if (*c as char).len_utf8() != 1 {
                return;
            }
            s.push(*c as char).unwrap();
        }
        //if let Ok(s) = heapless::String<N>::from_utf8(data.to_vec()) {
        let spec: Result<T, _> = s.parse();
        let expected = spec.map_err(|_| ());
        assert_eq!(expected, parse::<T>(&data).map_err(|_| ()));
        // let expected = spec.map_err(|e| e.kind().clone());
        // assert_eq!(expected, parse_u32(&data).map_err(|e| e.kind));
        // } else {
        //     //just make sure doesn't panic:
        //     let _ = parse::<u32>(&data);
        // }
    }
}
