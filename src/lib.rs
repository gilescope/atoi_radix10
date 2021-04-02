#![feature(unchecked_math)]

use core::arch::x86_64::{
    _mm_cvtsi128_si64, _mm_lddqu_si128, _mm_madd_epi16, _mm_maddubs_epi16, _mm_packus_epi32,
    _mm_set1_epi8, _mm_set_epi16, _mm_set_epi8, _mm_sub_epi16,
};

pub fn str_parse(s: &str) -> u64 {
    s.parse().unwrap()
}

pub fn naive_chars(s: &str) -> u64 {
    let mut result = 0;
    for digit in s.chars() {
        result *= 10;
        result += digit as u64 - '0' as u64;
    }
    result
}

pub fn naive_chars_iter(s: &str) -> u64 {
    s.chars().fold(0, |a, c| a * 10 + c as u64 - '0' as u64)
}

pub fn naive_chars_and(s: &str) -> u64 {
    s.chars().fold(0, |a, c| a * 10 + (c as u8 & 0x0f) as u64)
}

pub fn naive_bytes(s: &str) -> u64 {
    let mut result = 0;
    for digit in s.bytes() {
        result *= 10;
        result += (digit - b'0') as u64;
    }
    result
}

pub fn naive_bytes_iter(s: &str) -> u64 {
    s.bytes().fold(0, |a, c| a * 10 + (c - b'0') as u64)
}

pub fn naive_bytes_and(s: &str) -> u64 {
    s.bytes().fold(0, |a, c| a * 10 + (c & 0x0f) as u64)
}

pub fn naive_bytes_and_c16(s: &str) -> u64 {
    s.bytes()
        .take(16)
        .fold(0, |a, c| a * 10 + (c & 0x0f) as u64)
}

pub fn unrolled(s: &str) -> u64 {
    let mut result = 0;
    let bytes = s.as_bytes();
    result += (bytes[0] - b'0') as u64 * 1000000000000000;
    result += (bytes[1] - b'0') as u64 * 100000000000000;
    result += (bytes[2] - b'0') as u64 * 10000000000000;
    result += (bytes[3] - b'0') as u64 * 1000000000000;
    result += (bytes[4] - b'0') as u64 * 100000000000;
    result += (bytes[5] - b'0') as u64 * 10000000000;
    result += (bytes[6] - b'0') as u64 * 1000000000;
    result += (bytes[7] - b'0') as u64 * 100000000;
    result += (bytes[8] - b'0') as u64 * 10000000;
    result += (bytes[9] - b'0') as u64 * 1000000;
    result += (bytes[10] - b'0') as u64 * 100000;
    result += (bytes[11] - b'0') as u64 * 10000;
    result += (bytes[12] - b'0') as u64 * 1000;
    result += (bytes[13] - b'0') as u64 * 100;
    result += (bytes[14] - b'0') as u64 * 10;
    result += (bytes[15] - b'0') as u64;
    result
}

pub fn unrolled_unsafe(s: &str) -> u64 {
    let mut result = 0;
    let bytes = s.as_bytes();
    result += (unsafe { bytes.get_unchecked(0) } - b'0') as u64 * 1000000000000000;
    result += (unsafe { bytes.get_unchecked(1) } - b'0') as u64 * 100000000000000;
    result += (unsafe { bytes.get_unchecked(2) } - b'0') as u64 * 10000000000000;
    result += (unsafe { bytes.get_unchecked(3) } - b'0') as u64 * 1000000000000;
    result += (unsafe { bytes.get_unchecked(4) } - b'0') as u64 * 100000000000;
    result += (unsafe { bytes.get_unchecked(5) } - b'0') as u64 * 10000000000;
    result += (unsafe { bytes.get_unchecked(6) } - b'0') as u64 * 1000000000;
    result += (unsafe { bytes.get_unchecked(7) } - b'0') as u64 * 100000000;
    result += (unsafe { bytes.get_unchecked(8) } - b'0') as u64 * 10000000;
    result += (unsafe { bytes.get_unchecked(9) } - b'0') as u64 * 1000000;
    result += (unsafe { bytes.get_unchecked(10) } - b'0') as u64 * 100000;
    result += (unsafe { bytes.get_unchecked(11) } - b'0') as u64 * 10000;
    result += (unsafe { bytes.get_unchecked(12) } - b'0') as u64 * 1000;
    result += (unsafe { bytes.get_unchecked(13) } - b'0') as u64 * 100;
    result += (unsafe { bytes.get_unchecked(14) } - b'0') as u64 * 10;
    result += (unsafe { bytes.get_unchecked(15) } - b'0') as u64;
    result
}

pub fn unrolled_safe(s: &str) -> u64 {
    let mut result = 0;
    let bytes = s.get(..16).unwrap().as_bytes();
    result += (bytes[0] - b'0') as u64 * 1000000000000000;
    result += (bytes[1] - b'0') as u64 * 100000000000000;
    result += (bytes[2] - b'0') as u64 * 10000000000000;
    result += (bytes[3] - b'0') as u64 * 1000000000000;
    result += (bytes[4] - b'0') as u64 * 100000000000;
    result += (bytes[5] - b'0') as u64 * 10000000000;
    result += (bytes[6] - b'0') as u64 * 1000000000;
    result += (bytes[7] - b'0') as u64 * 100000000;
    result += (bytes[8] - b'0') as u64 * 10000000;
    result += (bytes[9] - b'0') as u64 * 1000000;
    result += (bytes[10] - b'0') as u64 * 100000;
    result += (bytes[11] - b'0') as u64 * 10000;
    result += (bytes[12] - b'0') as u64 * 1000;
    result += (bytes[13] - b'0') as u64 * 100;
    result += (bytes[14] - b'0') as u64 * 10;
    result += (bytes[15] - b'0') as u64;
    result
}

pub fn trick(s: &str) -> u64 {
    let (upper_digits, lower_digits) = s.split_at(8);
    parse_8_chars(upper_digits).unwrap() * 100000000 + parse_8_chars(lower_digits).unwrap()
}

pub fn trick2(s: &str) -> u64 {
    parse_u64(s).unwrap()
}

pub fn parse_u64(s: &str) -> Result<u64, ()> {
    let l = s.len();
    if l <= 8 {
        let mut res = parse_8_chars(s)?;
        if l < 8 {
            res = res / MULTIPLIER[MULTIPLIER.len() - 1 - (8 - l)] as u64
        }
        return Ok(res);
    }
    let (upper_digits, lower_digits) = s.split_at(l - 8);
    let res = match parse_8_chars(upper_digits)?
        .checked_mul(MULTIPLIER[MULTIPLIER.len() - 1 - (l - 8)] as u64)
    {
        Some(res) => res,
        None => return Err(()),
    }
    .checked_add(parse_8_chars(lower_digits)?);
    match res {
        Some(res) => Ok(res),
        None => return Err(()),
    }
}

pub fn trick3(src: &str) -> i64 {
    parse_signed64(src).unwrap()
}

pub fn parse_signed64(src: &str) -> Result<i64, ()> {
    if src.is_empty() {
        return Err(());
    }
    let (is_positive, digits) = match src.as_bytes()[0] {
        b'+' | b'-' if src[1..].is_empty() => {
            return Err(());
        }
        b'+' => (true, &src[1..]),
        b'-' => (false, &src[1..]),
        _ => (true, src),
    };
    let i = trick2(digits);
    if is_positive {
        if i > i64::MAX as u64 {
            return Err(());
        }
        Ok(i as i64)
    } else {
        if i > i64::MAX as u64 + 1 {
            return Err(());
        }
        match 0_i64.checked_sub(i as i64) {
            Some(res) => Ok(res),
            None => Err(()),
        }
    }
}

pub fn trick_128(s: &str) -> u64 {
    let s = s.as_ptr() as *const _;
    let mut chunk = 0_u128;
    unsafe {
        std::ptr::copy_nonoverlapping(s, &mut chunk, std::mem::size_of_val(&chunk));
    }

    // 1-byte mask trick (works on 8 pairs of single digits)
    let lower_digits = (chunk & 0x0f000f000f000f000f000f000f000f00) >> 8;
    let upper_digits = (chunk & 0x000f000f000f000f000f000f000f000f) * 10;
    let chunk = lower_digits + upper_digits;

    // 2-byte mask trick (works on 4 pairs of two digits)
    let lower_digits = (chunk & 0x00ff000000ff000000ff000000ff0000) >> 16;
    let upper_digits = (chunk & 0x000000ff000000ff000000ff000000ff) * 100;
    let chunk = lower_digits + upper_digits;

    // 4-byte mask trick (works on 2 pairs of four digits)
    let lower_digits = (chunk & 0x0000ffff000000000000ffff00000000) >> 32;
    let upper_digits = (chunk & 0x000000000000ffff000000000000ffff) * 10000;
    let chunk = lower_digits + upper_digits;

    // 8-byte mask trick (works on a pair of eight digits)
    let lower_digits = (chunk & 0x00000000ffffffff0000000000000000) >> 64;
    let upper_digits = (chunk & 0x000000000000000000000000ffffffff) * 100000000;
    let chunk = lower_digits + upper_digits;

    chunk as u64
}

pub fn trick_simd(s: &str) -> u64 {
    unsafe {
        let chunk = _mm_lddqu_si128(std::mem::transmute_copy(&s));
        let zeros = _mm_set1_epi8(b'0' as i8);
        let chunk = _mm_sub_epi16(chunk, zeros);

        let mult = _mm_set_epi8(1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10);
        let chunk = _mm_maddubs_epi16(chunk, mult);

        let mult = _mm_set_epi16(1, 100, 1, 100, 1, 100, 1, 100);
        let chunk = _mm_madd_epi16(chunk, mult);

        let chunk = _mm_packus_epi32(chunk, chunk);
        let mult = _mm_set_epi16(0, 0, 0, 0, 1, 10000, 1, 10000);
        let chunk = _mm_madd_epi16(chunk, mult);

        let chunk = _mm_cvtsi128_si64(chunk) as u64;
        ((chunk & 0xffffffff) * 100000000) + (chunk >> 32)
    }
}

// pub fn trick_simd_8(s: &str) -> u64 {
//     let (upper_digits, lower_digits) = s.split_at(8);
//     parse_8_chars_simd(lower_digits)
// }

fn parse_8_chars(s: &str) -> Result<u64, ()> {
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const MASK_LOW: u64 = 0x0f0f0f0f0f0f0f0fu64;
    const M3: u64 = 0x3030303030303030u64;
    let mut chunk = 0;
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const _,
            &mut chunk,
            std::mem::size_of_val(&chunk),
        );
    }

    // Make bit pattern regular if < 8 chars by prefixing with b'0's:
    let chunk = chunk | 0x3030303030303030u64 << s.len() * 8;

    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let x = chunk & MASK_LOW;
    const RESULT_MASK: u64 = !0u64 / 255 * 128;
    const N: u64 = 9;
    const N_MASK: u64 = !0u64 / 255 * (127 - N);
    if (chunk & MASK_HI) != M3 || (x + N_MASK | x) & RESULT_MASK > 0 {
        // _mm_cmpgt_epi8 would also work nicely here if available on target.
        return Err(());
    }

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
    Ok(chunk)
}

// fn parse_8_chars_simd(s: &str) -> u64 {
//     unsafe {
//         let chunk = _mm_loadu_si64(std::mem::transmute_copy(&s));
//         let zeros = _mm_set1_epi8(b'0' as i8);
//         let chunk = _mm_sub_epi16(chunk, zeros);
//
//         let mult = _mm_set_epi8(10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1);
//         let chunk = _mm_maddubs_epi16(chunk, mult);
//
//         let mult = _mm_set_epi16(100, 1, 100, 1, 100, 1, 100, 1);
//         let chunk = _mm_madd_epi16(chunk, mult);
//
//         let chunk = _mm_packus_epi32(chunk, chunk);
//         let mult = _mm_set_epi16(10000, 1, 10000, 1, 10000, 1, 10000, 1);
//         let chunk = _mm_madd_epi16(chunk, mult);
//
//         _mm_cvtsi128_si32(chunk) as u64
//     }
// }

pub fn trick_simd_c16(s: &str) -> u64 {
    let d: &mut [u8; 16] = &mut b"0000000000000000".clone();
    let b: &[u8] = s.as_bytes();
    d.copy_from_slice(b);

    unsafe {
        let chunk = _mm_lddqu_si128(std::mem::transmute_copy(&d));
        let zeros = _mm_set1_epi8(b'0' as i8);
        let chunk = _mm_sub_epi16(chunk, zeros);

        let mult = _mm_set_epi8(1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10);
        let chunk = _mm_maddubs_epi16(chunk, mult);

        let mult = _mm_set_epi16(1, 100, 1, 100, 1, 100, 1, 100);
        let chunk = _mm_madd_epi16(chunk, mult);

        let chunk = _mm_packus_epi32(chunk, chunk);
        let mult = _mm_set_epi16(0, 0, 0, 0, 1, 10000, 1, 10000);
        let chunk = _mm_madd_epi16(chunk, mult);

        let chunk = _mm_cvtsi128_si64(chunk) as u64;
        ((chunk & 0xffffffff) * 100000000) + (chunk >> 32)
    }
}

#[doc(hidden)]
trait FromStrRadixHelper: PartialOrd + Copy {
    fn min_value() -> Self;
    fn max_value() -> Self;
    fn from_u32(u: u32) -> Self;
    fn checked_mul(&self, other: u32) -> Option<Self>;
    fn mul(&self, other: u32) -> Self;
    fn checked_sub(&self, other: u32) -> Option<Self>;
    fn checked_add(&self, other: u32) -> Option<Self>;
    fn add(&self, other: u32) -> Self;
    fn checked_shl(&self, other: u32) -> Option<Self>;
    unsafe fn uunchecked_mul(&self, other: u32) -> Self;
    unsafe fn uunchecked_sub(&self, other: u32) -> Self;
    unsafe fn uunchecked_add(&self, other: u32) -> Self;
}

macro_rules! doit {
    ($($t:ty)*) => ($(impl FromStrRadixHelper for $t {
        // #[inline]
        // fn safe_len() -> usize { $safe_len }
        #[inline]
        fn min_value() -> Self { Self::MIN }
        #[inline]
        fn max_value() -> Self { Self::MAX }
        #[inline]
        fn from_u32(u: u32) -> Self { u as Self }
        #[inline(always)]
        fn checked_mul(&self, other: u32) -> Option<Self> {
            Self::checked_mul(*self, other as Self)
        }
        #[inline]
        fn mul(&self, other: u32) -> Self {
            *self * other as Self
        }
        #[inline]
        fn checked_sub(&self, other: u32) -> Option<Self> {
            Self::checked_sub(*self, other as Self)
        }
        #[inline(always)]
        fn checked_add(&self, other: u32) -> Option<Self> {
            Self::checked_add(*self, other as Self)
        }
        #[inline(always)]
        fn add(&self, other: u32) -> Self {
            *self + (other as Self)
        }
        #[inline]
        fn checked_shl(&self, other: u32) -> Option<Self> {
            Self::checked_shl(*self, other as u32)
        }
        #[inline]
        unsafe fn uunchecked_mul(&self, other: u32) -> Self {
            unsafe {
                Self::unchecked_mul(*self, other as Self)
            }
        }
        #[inline]
        unsafe fn uunchecked_sub(&self, other: u32) -> Self {
            unsafe {
                Self::unchecked_sub(*self, other as Self)
            }
        }
        #[inline]
        unsafe fn uunchecked_add(&self, other: u32) -> Self {
            unsafe {
                Self::unchecked_add(*self, other as Self)
            }
        }
    })*)
}
doit! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }

use std::{num::*, ops::Shr};

pub fn str_parse_unchecked(s: &str) -> u64 {
    from_str_radix_unchecked::<u64>(s, 10).unwrap()
}

fn from_str_radix_unchecked<T: FromStrRadixHelper>(src: &str, radix: u32) -> Result<T, ()> {
    assert!(
        radix >= 2 && radix <= 36,
        "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
        radix
    );

    if src.is_empty() {
        return Err(());
    }

    let is_signed_ty = T::from_u32(0) > T::min_value();

    // all valid digits are ascii, so we will just iterate over the utf8 bytes
    // and cast them to chars. .to_digit() will safely return None for anything
    // other than a valid ascii digit for the given radix, including the first-byte
    // of multi-byte sequences
    let src = src.as_bytes();

    let (is_positive, digits) = match src[0] {
        b'+' | b'-' if src[1..].is_empty() => {
            return Err(());
        }
        b'+' => (true, &src[1..]),
        b'-' if is_signed_ty => (false, &src[1..]),
        _ => (true, src),
    };

    let mut result = T::from_u32(0);
    if radix <= 16 && src.len() <= std::mem::size_of::<T>() * 2 - if is_signed_ty { 1 } else { 0 } {
        // The ALU can reorder these adds and do more in parallel
        // as each mul isn't dependent on the previous answer.
        unsafe {
            if is_positive {
                // The number is positive
                for &c in digits {
                    //let x  = c.wrapping_sub(b'0') as u32;
                    // if x > 9 {
                    //     return Err(());
                    // }
                    let x = match (c as char).to_digit(radix) {
                        Some(x) => x,
                        None => return Err(()),
                    };
                    result = result.uunchecked_mul(radix);
                    result = result.uunchecked_add(x);
                }
            } else {
                // The number is negative
                for &c in digits {
                    let x = match (c as char).to_digit(radix) {
                        Some(x) => x,
                        None => return Err(()),
                    };
                    result = result.uunchecked_mul(radix);
                    result = result.uunchecked_sub(x);
                }
            }
        }
    } else {
        if is_positive {
            // The number is positive
            for &c in digits {
                let x = match (c as char).to_digit(radix) {
                    Some(x) => x,
                    None => return Err(()),
                };
                result = match result.checked_mul(radix) {
                    Some(result) => result,
                    None => return Err(()),
                };
                result = match result.checked_add(x) {
                    Some(result) => result,
                    None => return Err(()),
                };
            }
        } else {
            // The number is negative
            for &c in digits {
                let x = match (c as char).to_digit(radix) {
                    Some(x) => x,
                    None => return Err(()),
                };
                result = match result.checked_mul(radix) {
                    Some(result) => result,
                    None => return Err(()),
                };
                result = match result.checked_sub(x) {
                    Some(result) => result,
                    None => return Err(()),
                };
            }
        }
    }
    Ok(result)
}

pub fn str_parse_multiplier(s: &str) -> u64 {
    from_str_radix_multiplier::<u64>(s, 10).unwrap()
}

fn from_str_radix_multiplier<T: FromStrRadixHelper>(src: &str, radix: u32) -> Result<T, ()> {
    assert!(
        radix >= 2 && radix <= 36,
        "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
        radix
    );

    if src.is_empty() {
        return Err(());
    }

    // Compiler can't compile the following:
    //const is_signed_ty : bool =  T::MIN < T::MAX;
    //If it could I might push for T::ZERO to be defined.
    let is_signed_ty: bool = T::from_u32(0) > T::min_value();

    // all valid digits are ascii, so we will just iterate over the utf8 bytes
    // and cast them to chars. .to_digit() will safely return None for anything
    // other than a valid ascii digit for the given radix, including the first-byte
    // of multi-byte sequences
    let src = src.as_bytes();

    let (is_positive, digits) = match src[0] {
        b'+' | b'-' if src[1..].is_empty() => {
            return Err(());
        }
        b'+' => (true, &src[1..]),
        b'-' if is_signed_ty => (false, &src[1..]),
        _ => (true, src),
    };

    let mut result = T::from_u32(0);
    if radix == 10 {
        // The ALU can reorder these adds and do more in parallel
        // as each mul isn't dependent on the previous answer.
        let mut todo = digits.len();
        let mut idx = MULTIPLIER.len() - todo.min(9);
        if is_positive {
            unsafe {
                for &c in digits {
                    if idx == MULTIPLIER.len() {
                        todo -= 9;
                        idx = MULTIPLIER.len() - todo.min(9);
                        result = result.mul(*MULTIPLIER.get_unchecked(idx - 1));
                    }
                    let mut x = match (c as char).to_digit(radix) {
                        Some(x) => x,
                        None => return Err(()),
                    };
                    x = match MULTIPLIER.get_unchecked(idx).checked_mul(x) {
                        Some(result) => result,
                        None => return Err(()),
                    };
                    result = match result.checked_add(x) {
                        Some(result) => result,
                        None => return Err(()),
                    };

                    idx += 1;
                }
            }
        } else {
            if is_signed_ty {
                unsafe {
                    for &c in digits {
                        if idx == MULTIPLIER.len() {
                            todo -= 9;
                            idx = MULTIPLIER.len() - todo.min(9);
                            result = result.mul(*MULTIPLIER.get_unchecked(idx - 1));
                        }
                        let mut x = match (c as char).to_digit(radix) {
                            Some(x) => x,
                            None => return Err(()),
                        };
                        x = match MULTIPLIER.get_unchecked(idx).checked_mul(x) {
                            Some(result) => result,
                            None => return Err(()),
                        };
                        result = match result.checked_sub(x) {
                            Some(result) => result,
                            None => return Err(()),
                        };

                        idx += 1;
                    }
                }
            }
        }
    } else {
        //snipped
    }
    Ok(result)
}

const MULTIPLIER: &[u32] = &[
    1_000_000_000,
    100_000_000,
    10_000_000,
    1_000_000,
    100_000,
    10_000,
    1_000,
    100,
    10,
    1,
];
const XMULTIPLIER: &[[u32; 10]] = &[
    [
        1_000_000_000,
        100_000_000,
        10_000_000,
        1_000_000,
        100_000,
        10_000,
        1_000,
        100,
        10,
        1,
    ],
    [
        1_000_000_000,
        200_000_000,
        20_000_000,
        2_000_000,
        200_000,
        20_000,
        2_000,
        200,
        20,
        2,
    ],
    [
        1_000_000_000,
        300_000_000,
        30_000_000,
        3_000_000,
        300_000,
        30_000,
        3_000,
        300,
        30,
        3,
    ],
    [
        1_000_000_000,
        400_000_000,
        40_000_000,
        4_000_000,
        400_000,
        40_000,
        4_000,
        400,
        40,
        4,
    ],
    [
        1_000_000_000,
        500_000_000,
        50_000_000,
        5_000_000,
        500_000,
        50_000,
        5_000,
        500,
        50,
        5,
    ],
    [
        1_000_000_000,
        600_000_000,
        60_000_000,
        6_000_000,
        600_000,
        60_000,
        6_000,
        600,
        60,
        6,
    ],
    [
        1_000_000_000,
        700_000_000,
        70_000_000,
        7_000_000,
        700_000,
        70_000,
        7_000,
        700,
        70,
        7,
    ],
    [
        1_000_000_000,
        800_000_000,
        80_000_000,
        8_000_000,
        800_000,
        80_000,
        8_000,
        800,
        80,
        8,
    ],
    [
        1_000_000_000,
        900_000_000,
        90_000_000,
        9_000_000,
        900_000,
        90_000,
        9_000,
        900,
        90,
        9,
    ],
];
