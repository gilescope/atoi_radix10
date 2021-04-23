#![feature(int_error_matching)]
use std::str::FromStr;

mod parse_i16;
mod parse_i8;
mod parse_u16;
mod parse_u32;
mod parse_u8;
mod parse_i32;
mod parse_i64;
mod parse_u128;
mod parse_u64;
mod parse_i128;

pub use parse_i16::{parse_i16, parse_i16_challenger};
pub use parse_i8::{parse_i8, parse_i8_challenger};
pub use parse_u16::{parse_u16, parse_u16_challenger};
pub use parse_u32::{parse_u32, parse_u32_challenger};
pub use parse_u8::{parse_u8, parse_u8_challenger};
pub use parse_i32::{parse_i32, parse_i32_challenger};
pub use parse_u64::{parse_u64, parse_u64_challenger};
pub use parse_i64::{parse_i64, parse_i64_challenger};
pub use parse_u128::{parse_u128, parse_u128_challenger};
pub use parse_i128::{parse_i128, parse_i128_challenger};

pub fn std_parse<T>(s: &str) -> Result<T, ()>
where
    T: FromStr,
{
    s.parse().map_err(|_| ())
}

pub fn cluatoi_parse_u32(s: &str) -> u32 {
    use cluatoi::Atoi;
    u32::atoi(s.as_bytes()).unwrap()
}

pub fn cluatoi_parse_u16(s: &str) -> u16 {
    use cluatoi::Atoi;
    u16::atoi(s.as_bytes()).unwrap()
}

pub fn cluatoi_parse_u8(s: &str) -> u8 {
    use cluatoi::Atoi;
    u8::atoi(s.as_bytes()).unwrap()
}

//bit faster than std
pub fn btoi_parse_u32(s: &str) -> u32 {
    btoi::btoi(s.as_bytes()).unwrap()
}

//atoi crate about the same speed as std.
pub fn atoi_parse_u32(s: &str) -> u32 {
    atoi::atoi::<u32>(s.as_bytes()).unwrap()
}

const PLUS: u8 = b'+'.wrapping_sub(b'0');
const MINUS: u8 = b'-'.wrapping_sub(b'0');

use core::num::IntErrorKind;
//use core::num::ParseIntError;
#[derive(Debug, Eq, PartialEq)]
pub struct ParseIntError2 {
    pub kind: IntErrorKind,
}

type PIE = ParseIntError2;

#[inline]
fn parse_16_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;

    //let mut chunk: u128 = 0u128;
    unsafe {
        //std::ptr::copy_nonoverlapping(s.as_ptr() as *const u128, &mut chunk, 1);

        let chunk = *(s.as_ptr() as *const u128) ^ ASCII_ZEROS;
        if (chunk & MASK_HI)
            | (chunk + 0x76767676767676767676767676767676u128
                & 0x80808080808080808080808080808080u128)
            == 0
        {
            // 1-byte mask trick (works on 8 pairs of single digits)
            let lower_digits = (chunk & 0x0f000f000f000f000f000f000f000f00) >> 8;
            let upper_digits = (chunk & 0x000f000f000f000f000f000f000f000f) * 10;
            let chunk = lower_digits + upper_digits;

            // 2-byte mask trick (works on 4 pairs of two digits)
            let lower_digits = (chunk & 0x00ff000000ff000000ff000000ff0000) >> 16;
            let upper_digits = (chunk & 0x000000ff000000ff000000ff000000ff) * 100;
            let chunk = lower_digits + upper_digits;

            // 4-byte mask trick (works on 2 pair of four digits)
            let lower_digits = (chunk & 0x0000ffff000000000000ffff00000000) >> 32;
            let upper_digits = (chunk & 0x000000000000ffff000000000000ffff) * 100_00;
            let chunk = lower_digits + upper_digits;

            // 8-byte mask trick (works on a pair of eight digits)
            let lower_digits = (chunk & 0x00000000ffffffff0000000000000000) >> 64;
            let upper_digits = (chunk & 0x000000000000000000000000ffffffff) * 100_00_00_00;
            let chunk = lower_digits + upper_digits;
            Ok(chunk as u64) //u64 can guarantee to contain 19 digits.
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

#[inline]
fn parse_8_chars(s: &[u8]) -> Result<u32, PIE> {
    debug_assert!(s.len() >= 8);
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;

    unsafe {
        //let chunk = core::mem::MaybeUninit::<u64>::uninit();
        //let mut chunk: u64 = std::mem::transmute(chunk);
        //std::ptr::copy_nonoverlapping(s.as_ptr() as *const u64, &mut chunk, 1);

        let chunk = *(s.as_ptr() as *const u64) ^ ASCII_ZEROS;
        if (chunk & MASK_HI) | (chunk + 0x7676767676767676u64 & 0x8080808080808080u64) == 0 {
            // 1-byte mask trick (works on 4 pairs of single digits)
            let lower_digits = (chunk & 0x0f000f000f000f00) >> 8;
            let upper_digits = (chunk & 0x000f000f000f000f) * 10;
            let chunk = lower_digits + upper_digits;

            // 2-byte mask trick (works on 2 pairs of two digits)
            let lower_digits = (chunk & 0x00ff000000ff0000) >> 16;
            let upper_digits = (chunk & 0x000000ff000000ff) * 100;
            let chunk = lower_digits + upper_digits;

            // 4-byte mask trick (works on a pair of four digits)
            let lower_digits = (chunk & 0x0000ffff00000000) >> 32;
            let upper_digits = (chunk & 0x000000000000ffff) * 10000;
            let chunk = lower_digits + upper_digits;
            Ok(chunk as u32) //u32 can guarantee to contain 9 digits.
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

// //Learned: Expanding to u64 costs too much.
// #[inline]
// fn parse_6_chars2(s: &[u8]) -> Result<u32, PIE> {
//     //SAFETY:
//     debug_assert!(s.len() >= 6);

//     const MASK_HI: u32 = 0xf0f0f0f0u32;
//     const ASCII_ZEROS: u32 = 0x30303030u32;
//     let mut chunk: u32 = 0;
//     const MASK_HI2: u16 = 0xf0f0u16;
//     const ASCII_ZEROS2: u16 = 0x3030u16;//0b0011__0000_0011_0000
//     let mut chunk2: u16 = 0;

//     unsafe {
//         std::ptr::copy_nonoverlapping(s.as_ptr() as *const u32, &mut chunk, 1);
//         std::ptr::copy_nonoverlapping(s.get_unchecked(4..).as_ptr() as *const u16, &mut chunk2, 1);
//     }

//     // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
//     let chunk = chunk ^ ASCII_ZEROS;
//     let chunk2 = chunk2 ^ ASCII_ZEROS2;
//     if (chunk & MASK_HI) + (chunk + 0x76767676u32 & 0x80808080u32) +
//         (chunk2 & MASK_HI2) as u32 + (chunk2 + 0x7676u16 & 0x8080u16) as u32 == 0 {
//         // 1-byte mask trick (works on 4 pairs of single digits)
//         let lower_digits = (chunk & 0x0f000f00) >> 8;
//         let upper_digits = (chunk & 0x000f000f) * 10;
//         let chunk = lower_digits + upper_digits;

//         // 2-byte mask trick (works on 2 pairs of two digits)
//         let lower_digits = (chunk & 0x00ff0000) >> 16;
//         let upper_digits = (chunk & 0x000000ff) * 100;
//         let chunk = lower_digits + upper_digits;

//         let lower_digits = (chunk2 & 0x0f00) >> 8;
//         let upper_digits = (chunk2 & 0x000f) * 10;
//         Ok(chunk as u32 * 100 + (lower_digits + upper_digits) as u32) //u16 can guarantee to hold 4 digits
//     } else {
//         Err(PIE {
//             kind: IntErrorKind::InvalidDigit,
//         })
//     }
// }

// #[inline]
// fn check_2_chars(s: &[u8]) -> bool {
//     //SAFETY:
//     debug_assert!(s.len() >= 2);
//     unsafe {
//         //std::ptr::copy_nonoverlapping(s.get_unchecked(4..).as_ptr() as *const u16, &mut chunk2, 1);
//         let chunk = *(s.get_unchecked(..2).as_ptr() as *const u16) ^ 0x3030u16;
//         (chunk & 0xf0f0u16) | (chunk + 0x7676u16 & 0x8080u16) == 0
//     }
// }

#[inline]
fn parse_4_chars(s: &[u8]) -> Result<u16, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const ASCII_ZEROS: u32 = 0x30303030u32;
    //let mut chunk: u32 = 0;

    unsafe {
        //        std::ptr::copy_nonoverlapping(s.as_ptr() as *const u32, &mut chunk, 1);

        // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
        let chunk = *(s.as_ptr() as *const u32) ^ ASCII_ZEROS;
        if (chunk & MASK_HI) | (chunk + 0x76767676u32 & 0x80808080u32) == 0 {
            // 1-byte mask trick (works on 4 pairs of single digits)
            let lower_digits = (chunk & 0x0f000f00) >> 8;
            let upper_digits = (chunk & 0x000f000f) * 10;
            let chunk = lower_digits + upper_digits;

            // 2-byte mask trick (works on 2 pairs of two digits)
            let lower_digits = (chunk & 0x00ff0000) >> 16;
            let upper_digits = (chunk & 0x000000ff) * 100;
            let chunk = lower_digits + upper_digits;
            Ok(chunk as u16) //u16 can guarantee to hold 4 digits
        } else {
            Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    }
}

#[inline]
fn parse_2_chars(s: &[u8]) -> Result<u8, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    const MASK_HI: u16 = 0xf0f0u16;
    const ASCII_ZEROS: u16 = 0x3030u16; //0b0011__0000_0011_0000

    unsafe {
        // let mut chunk: u16 = 0;
        // std::ptr::copy_nonoverlapping(s.as_ptr() as *const u16, &mut chunk, 1);

        let chunk = *(s.as_ptr() as *const u16) ^ ASCII_ZEROS;
        if (chunk & MASK_HI) | (chunk + 0x7676u16 & 0x8080u16) == 0 {
            // 1-byte mask trick (works on a pair of single digits)
            let lower_digits = (chunk & 0x0f00) >> 8;
            let upper_digits = (chunk & 0x000f) * 10;
            let chunk = lower_digits + upper_digits;
            Ok(chunk as u8) // u8 can guarantee to hold 2 chars.
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

// Good sized christmas tree:
const TENS_U64: &[u64] = &[
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
];

// Biggest christmas tree:
const TENS_U128: &[u128] = &[
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
    100_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000_000_000_000,
    1_000_000_000_000_000_000_000_000_000_000_000_000,
    10_000_000_000_000_000_000_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000_000_000_000_000,
];

#[cfg(test)]
mod tests {
    use super::*;
    use paste::paste;

    macro_rules! gen_tests {
        ($target_type:ty, $min:expr, $max:expr, $step: expr, $max_chars: literal,$postfix: literal, $specific: literal) => {
            paste! {
                #[test]
                fn [<test_ $target_type _specific $postfix>]() {
                    let s = $specific;
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "fail to parse: '{}'", &s);
                }

                #[test]
                fn [<test_invalid_ascii_ $target_type $postfix>]() {
                    for &ascii in [b':', b'/'].iter() {
                        for i in 1..$max_chars {
                            let vec = vec![b'1'; i];
                            for j in 1..i {
                                let mut v = vec.clone();
                                v[j] = ascii;
                                let s = String::from_utf8_lossy(&v[..]);
                                assert_eq!(Err(()), [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "parsing `{}`", s);
                            }
                        }
                    }
                }

                #[test]
                fn [<test_invalid_too_big_ $target_type $postfix>]() {
                    let mut s = ($target_type::MAX as $target_type).to_string();
                    s.push('1');
                    assert_eq!(
                        Err(PIE {
                            kind: IntErrorKind::PosOverflow
                        }),
                        [<parse_ $target_type $postfix>](&s)
                    );
                }

                #[test]
                fn [<test_empty_ $target_type $postfix>]() {
                    assert_eq!(
                        Err(PIE {
                            kind: IntErrorKind::Empty
                        }),
                        [<parse_ $target_type $postfix>]("")
                    );
                }

                #[test]
                fn [<test_ $target_type $postfix>]() {
                    for i in ($min..$max as $target_type).step_by($step) {
                        let s = i.to_string();
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[test]
                fn [<test_ $target_type _plus $postfix>]() {
                    for i in ($min..$max as $target_type).step_by($step) {
                        let mut s = i.to_string();
                        s.insert(0, '+');
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }
            }
        }
    }

    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "", "1");
    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "_challenger", "1");

    gen_tests!(i8, i8::MIN, i8::MAX, 1, 3, "", "1");
    gen_tests!(i8, i8::MIN, i8::MAX, 1, 3, "_challenger", "1");

    gen_tests!(u16, u16::MIN, u16::MAX, 1, 5, "", "1");
    gen_tests!(u16, u16::MIN, u16::MAX, 1, 5, "_challenger", "1");

    gen_tests!(i16, i16::MIN, i16::MAX, 1, 5, "", "1");
    gen_tests!(i16, i16::MIN, i16::MAX, 1, 5, "_challenger", "1");

    gen_tests!(u32, u32::MIN, u32::MAX, 10_301, 10, "", "1");
    gen_tests!(u32, u32::MIN, u32::MAX, 10_301, 10, "_challenger", "1");

    gen_tests!(i32, i32::MIN, i32::MAX, 10_301, 10, "", "1");
    gen_tests!(i32, i32::MIN, i32::MAX, 10_301, 10, "_challenger", "1");

    gen_tests!(u64, u64::MIN, u64::MAX, 100_301_000_000_000, 20, "", "1");
    gen_tests!(u64, u64::MIN, u64::MAX, 100_301_000_000_000, 20, "_challenger", "1");

    gen_tests!(i64, i64::MIN, i64::MAX, 100_301_000_000_000, 19, "", "-999993949854775808");

    gen_tests!(i64, i64::MIN, i64::MAX, 100_301_000_000_000, 19, "_challenger", "1");

    gen_tests!(u128, u64::MIN as u128, u64::MAX, 100_301_000_000_000, 39, "", "+0");
    gen_tests!(
        u128,
        u64::MIN as u128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );

    gen_tests!(i128, u64::MIN as i128, u64::MAX, 100_301_000_000_000, 39, "", "-170141183460469231731687303715884105728");
    gen_tests!(
        i128,
        u64::MIN as i128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );
}
