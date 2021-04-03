//#![feature(unchecked_math)]

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
    parse_8_chars_unchecked(upper_digits) * 100000000 + parse_8_chars_unchecked(lower_digits)
}

pub fn trick_with_checks(s: &str) -> u64 {
    parse_u64(s).unwrap()
}

pub fn parse_u64(mut s: &str) -> Result<u64, ()> {
    if s.as_bytes()[0] == b'+' {
        s = &s[1..];
    }
    let l = s.len();
    if l <= 8 {
        if l == 0 {
            return Err(());
        }
        return parse_8_chars(s);
    }
    let (upper_digits, lower_digits) = s.split_at(l - 8);
    let res = match parse_8_chars(upper_digits)?
        .checked_mul(MULTIPLIER[MULTIPLIER.len() - 1 - (l - 8)] as u64)
    {
        Some(res) => res,
        None => return Err(()),
    };
    match res.checked_add(parse_8_chars(lower_digits)?) {
        Some(res) => Ok(res),
        None => return Err(()),
    }
}

pub fn trick_with_checks_i64(src: &str) -> i64 {
    parse_signed64(src).unwrap()
}

pub fn parse_signed64(src: &str) -> Result<i64, ()> {
    let (is_positive, digits) = match src.as_bytes().get(0) {
        None => { return Err(()); }
        Some(b'-') => (false, &src[1..]),
        Some(_) => (true, src),
    };
    let i = parse_u64(digits)?;
    if is_positive {
        if i > i64::MAX as u64 {
            return Err(());
        }
        Ok(i as i64)
    } else {
        // Negative
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
    let l = s.len();
    // if l == 1 {
    //     let val = s.as_bytes()[0].wrapping_sub(b'0');
    //     return if val <= 9 {
    //         Ok(val as u64)
    //     } else {
    //         Err(())
    //     }
    // }
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const MASK_LOW: u64 = 0x0f0f0f0f0f0f0f0fu64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;
    let mut chunk = 0;
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const _,
            &mut chunk,
            std::mem::size_of_val(&chunk),
        );

        // SAFETY: Unknown memory due to < 8 len replaced with with b'0's:
        chunk = chunk << ((8 - l) * 8) | 0x3030303030303030u64 >> l * 8;
    }

    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let x = chunk & MASK_LOW;
    const RESULT_MASK: u64 = !0u64 / 255 * 128;
    const N: u64 = 9;
    const N_MASK: u64 = !0u64 / 255 * (127 - N);
    if (chunk & MASK_HI) - ASCII_ZEROS | ((x + N_MASK | x) & RESULT_MASK) != 0 {
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

fn parse_8_chars_unchecked(s: &str) -> u64 {
    let mut chunk = 0;
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const _,
            &mut chunk,
            std::mem::size_of_val(&chunk),
        );
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
    chunk
}

// fn parse_8_chars_simd(s: &str) -> u64 {
//     unsafe {
//         let chunk = _mm_loadu_si64(std::mem::transmute_copy(&s));
//         let zeros = _mm_set1_epi8(b'0' as i8);
//         let chunk = _mm_sub_epi16(chunk, zeros);

//         let mult = _mm_set_epi8(10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1);
//         let chunk = _mm_maddubs_epi16(chunk, mult);

//         let mult = _mm_set_epi16(100, 1, 100, 1, 100, 1, 100, 1);
//         let chunk = _mm_madd_epi16(chunk, mult);

//         let chunk = _mm_packus_epi32(chunk, chunk);
//         let mult = _mm_set_epi16(10000, 1, 10000, 1, 10000, 1, 10000, 1);
//         let chunk = _mm_madd_epi16(chunk, mult);

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