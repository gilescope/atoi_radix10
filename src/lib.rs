#![cfg_attr(not(feature = "std"), no_std)]
#![feature(int_error_matching)]
#![feature(unchecked_math)]
#![feature(core_intrinsics)]

mod parse;

mod parse_i128;
mod parse_i16;
mod parse_i32;
mod parse_i64;
mod parse_i8;
mod parse_u128;
mod parse_u16;
mod parse_u32;
mod parse_u64;
mod parse_u8;
mod trees;

//pub(crate) use tree::*;

pub(crate) use parse::parse;
pub use parse_i128::{parse_i128, parse_i128_challenger};
pub use parse_i16::{parse_i16, parse_i16_challenger};
pub use parse_i32::{parse_i32, parse_i32_challenger};
pub use parse_i64::{parse_i64, parse_i64_challenger};
pub use parse_i8::{parse_i8, parse_i8_challenger};
pub use parse_u128::{parse_u128, parse_u128_challenger};
pub use parse_u16::{parse_u16, parse_u16_challenger};
pub use parse_u32::{parse_u32, parse_u32_challenger};
pub use parse_u64::{parse_u64, parse_u64_challenger};
pub use parse_u8::{parse_u8, parse_u8_challenger};

#[cfg(feature = "std")]
pub fn std_parse<T>(s: &str) -> Result<T, ()>
where
    T: std::str::FromStr,
{
    s.parse().map_err(|_| ())
}

// pub fn cluatoi_parse_u32(s: &str) -> u32 {
//     use cluatoi::Atoi;
//     u32::atoi(s.as_bytes()).unwrap()
// }

// pub fn cluatoi_parse_u16(s: &str) -> u16 {
//     use cluatoi::Atoi;
//     u16::atoi(s.as_bytes()).unwrap()
// }

// pub fn cluatoi_parse_u8(s: &str) -> u8 {
//     use cluatoi::Atoi;
//     u8::atoi(s.as_bytes()).unwrap()
// }

// //bit faster than std
// pub fn btoi_parse_u32(s: &str) -> u32 {
//     btoi::btoi(s.as_bytes()).unwrap()
// }

// //atoi crate about the same speed as std.
// pub fn atoi_parse_u32(s: &str) -> u32 {
//     atoi::atoi::<u32>(s.as_bytes()).unwrap()
// }

const PLUS: u8 = b'+'.wrapping_sub(b'0');
const MINUS: u8 = b'-'.wrapping_sub(b'0');

use core::num::IntErrorKind;
//use core::num::ParseIntError;
#[derive(Debug, Eq, PartialEq)]
pub struct ParseIntError2 {
    pub kind: IntErrorKind,
}

//TODO: At the moment having more than one arm in the enum
// leads to a 3ns slowdown for 128bit types.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntErrorKind3 {
    /// Value being parsed is empty.
    ///
    /// Among other causes, this variant will be constructed when parsing an empty string.
    ///Empty,
    /// Contains an invalid digit in its context.
    ///
    /// Among other causes, this variant will be constructed when parsing a string that
    /// contains a non-ASCII char.
    ///
    /// This variant is also constructed when a `+` or `-` is misplaced within a string
    /// either on its own or in the middle of a number.
    InvalidDigit,
    // Integer is too large to store in target integer type.
    //  PosOverflow,
    // Integer is too small to store in target integer type.
    // NegOverflow,
    // Value was Zero
    //
    // This variant will be emitted when the parsing string has a value of zero, which
    // would be illegal for non-zero types.
    // Zero,
}

#[derive(Debug, Eq, PartialEq)]
pub struct ParseIntError3 {
    pub kind: IntErrorKind3,
}

type PIE = ParseIntError2;

#[cfg(not(target_feature = "avx"))]
#[cfg(target_endian = "little")]
#[inline]
pub fn parse_32_chars(mut s: &[u8]) -> Result<u128, PIE> {
    unsafe {
        let val16 = parse_16_chars(&s)? as u128;
        s = &s.get_unchecked(16..);
        let res = val16 * 1_0000_0000_0000_0000;

        // Do the same thing again as a parse_32_chars fn would need 256bits.
        let val16 = parse_16_chars(&s)? as u128;
        Ok(res + val16)
    }
}

#[cfg(target_feature = "avx")]
#[inline]
pub fn parse_32_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 32);

    use core::arch::x86_64::{
        __m256i, _mm256_lddqu_si256, _mm256_madd_epi16, _mm256_maddubs_epi16, _mm256_packus_epi32,
        _mm256_set1_epi8, _mm256_set_epi16, _mm256_set_epi8, _mm256_sub_epi16,
    };
    use core_simd::*;

    unsafe {
        let chunk = _mm256_lddqu_si256(std::mem::transmute_copy(&s));
        let zeros = _mm256_set1_epi8(b'0' as i8);
        let chunk = _mm256_sub_epi16(chunk, zeros); //will wrap

        let zero_to_lowest = i8x32::splat(-128);
        let chunkk: i8x32 = chunk.into();
        let digits_at_lowest = chunkk + zero_to_lowest;

        let upper_bound = i8x32::splat(-128 + 10);
        let range_chk1 = i8x32::lanes_lt(digits_at_lowest, upper_bound);

        let is_valid = range_chk1.all();

        let mult = _mm256_set_epi8(
            1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1,
            10, 1, 10, 1, 10, 1, 10,
        );
        let chunk = _mm256_maddubs_epi16(chunk, mult);

        let mult = _mm256_set_epi16(
            1, 100, 1, 100, 1, 100, 1, 100, 1, 100, 1, 100, 1, 100, 1, 100,
        );
        let chunk = _mm256_madd_epi16(chunk, mult);

        let chunk = _mm256_packus_epi32(chunk, chunk);
        let mult = _mm256_set_epi16(
            0, 0, 0, 0, 0, 0, 0, 0, 1, 10000, 1, 10000, 1, 10000, 1, 10000,
        );
        let chunk: __m256i = _mm256_madd_epi16(chunk, mult);

        let chunk: i64x4 = chunk.into();
        let chunk: u64 = chunk.to_array()[3].unsigned_abs() * 1_0000_0000_0000_0000
            + chunk.to_array()[2].unsigned_abs();

        if is_valid {
            Ok(chunk)
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

#[cfg(target_endian = "little")]
#[inline]
pub fn parse_16_chars_og1(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;

    //let mut chunk: u128 = 0u128;

    //std::ptr::copy_nonoverlapping(s.as_ptr() as *const u128, &mut chunk, 1);

    let chunk = unsafe { *(s.as_ptr() as *const u128) ^ ASCII_ZEROS };
    if (chunk & MASK_HI)
        | (chunk.wrapping_add(0x76767676767676767676767676767676u128)
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

/// Almost as good as SIMD...
#[cfg(not(target_feature = "sse2"))]
#[cfg(target_endian = "little")]
#[inline]
pub fn parse_16_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;

    let chunk = unsafe { *(s.as_ptr() as *const u128) ^ ASCII_ZEROS };
    let chunk_og = chunk;

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

    let chk = chunk_og.wrapping_add(0x76767676767676767676767676767676u128);
    // 8-byte mask trick (works on a pair of eight digits)
    let lower_digits = ((chunk & 0x00000000ffffffff0000000000000000) >> 64) as u64;
    let upper_digits = (chunk as u64) * 100_00_00_00; //& 0x00000000ffffffff
    let chunk = lower_digits + upper_digits;

    if (chunk_og & MASK_HI) | (chk & 0x80808080808080808080808080808080u128) == 0 {
        Ok(chunk) //u64 can guarantee to contain 19 digits.
    } else {
        return Err(PIE {
            kind: IntErrorKind::InvalidDigit,
        });
    }
}

#[cfg(target_feature = "sse2")]
#[inline]
pub fn parse_16_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);

    use core::arch::x86_64::{
        __m128i, _mm_lddqu_si128, _mm_madd_epi16, _mm_maddubs_epi16, _mm_packus_epi32,
    };
    use core_simd::*;
    unsafe {
        //TODO: waiting on https://github.com/rust-lang/stdsimd/issues/102
        let chunk: __m128i = _mm_lddqu_si128(std::mem::transmute_copy(&s)); //) _mm_lddqu_si128
        let chunk: i8x16 = chunk.into(); //) _mm_lddqu_si128
        let zeros = i8x16::splat(b'0' as i8);

        let chunk = chunk - zeros; //will wrap

        let zero_to_lowest = i8x16::splat(-128);
        let digits_at_lowest = chunk + zero_to_lowest;

        let upper_bound = i8x16::splat(-128 + 10);
        let range_chk1 = i8x16::lanes_lt(digits_at_lowest, upper_bound);
        let is_valid = range_chk1.all();

        let mult = i8x16::from_array([10_i8, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1]);

        let chunk: __m128i = _mm_maddubs_epi16(chunk.into(), mult.into());
        let chunk: i8x16 = chunk.into();

        let mult: i16x8 = i16x8::from_array([100, 1, 100, 1, 100, 1, 100, 1]);
        let chunk: __m128i = chunk.into();
        let chunk: i16x8 = chunk.into();

        let chunk: __m128i = _mm_madd_epi16(chunk.into(), mult.into());
        let chunk: i16x8 = chunk.into();

        let chunk = _mm_packus_epi32(chunk.into(), chunk.into());
        let mult = i16x8::from_array([10000, 1, 10000, 1, 10000, 1, 10000, 1]);

        let chunk: __m128i = _mm_madd_epi16(chunk.into(), mult.into());
        let chunk: i16x8 = chunk.into();
        let chunk: __m128i = chunk.into();
        let chunk: i64x2 = chunk.into();
        let chunk: u64 = chunk.to_array()[1].unsigned_abs(); //this could just be a transmute

        let chunk = ((chunk & 0xffffffff) * 1_0000_0000) + (chunk >> 32);
        if is_valid {
            Ok(chunk)
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

#[cfg(target_endian = "little")]
#[inline]
pub fn parse_8_chars(s: &[u8]) -> Result<u32, PIE> {
    debug_assert!(s.len() >= 8);
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;

    let chunk = unsafe { *(s.as_ptr() as *const u64) ^ ASCII_ZEROS };
    let valid = (chunk & MASK_HI)
        | (chunk.wrapping_add(0x7676767676767676u64) & 0x8080808080808080u64)
        == 0;

    // 1-byte mask trick (works on 4 pairs of single digits)
    let lower_digits = (chunk & 0x0f000f000f000f00) >> 8;
    let upper_digits = (chunk & 0x000f000f000f000f) * 10; //Compiler does *8 + *2
    let chunk = lower_digits + upper_digits;

    // 2-byte mask trick (works on 2 pairs of two digits)
    let lower_digits = (chunk & 0x00ff000000ff0000) >> 16;
    let upper_digits = (chunk & 0x000000ff000000ff) * 100;
    let chunk = lower_digits + upper_digits;

    // 4-byte mask trick (works on a pair of four digits)
    let lower_digits = ((chunk & 0x0000ffff00000000) >> 32) as u32;
    let upper_digits = (chunk as u32) * 10000; //10000 = 8192 + 1024 + 512 + 256+ 16
                                               //8192 + 2048 + 16 - 256  //& 0x0000ffff

    //We do this before the if shaving 300ps.
    let chunk = lower_digits + upper_digits;

    if valid {
        Ok(chunk) //u32 can guarantee to contain 9 digits.
    } else {
        Err(PIE {
            kind: IntErrorKind::InvalidDigit,
        })
    }
}

//Learned: Expanding to u64 costs too much.
#[inline]
pub fn parse_6_chars(s: &[u8]) -> Result<u32, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 6);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const ASCII_ZEROS: u32 = 0x30303030u32;
    const MASK_HI2: u16 = 0xf0f0u16;
    const ASCII_ZEROS2: u16 = 0x3030u16; //0b0011__0000_0011_0000

    let chunk = unsafe { *(s.as_ptr() as *const u32) };
    let chunk2 = unsafe { *(s.get_unchecked(4..).as_ptr() as *const u16) };

    // let chunk = *(s.as_ptr() as *const u32) as u64;
    // let chunk2 = (*(s.get_unchecked(4..).as_ptr() as *const u16) as u64) << ;

    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let chunk = chunk ^ ASCII_ZEROS;
    let chunk2 = chunk2 ^ ASCII_ZEROS2;
    let chunk_og = chunk;
    let chunk2_og = chunk2;

    // 1-byte mask trick (works on 4 pairs of single digits)
    let lower_digits = (chunk & 0x0f000f00) >> 8;
    let upper_digits = (chunk & 0x000f000f) * 10;
    let chunk = lower_digits + upper_digits;

    // 2-byte mask trick (works on 2 pairs of two digits)
    let lower_digits = (chunk & 0x00ff0000) >> 16;
    let upper_digits = (chunk & 0x000000ff) * 100;
    let chunk = lower_digits + upper_digits;
    let chunk = chunk * 100;

    let lower_digits = (chunk2 & 0x0f00) >> 8;
    let upper_digits = (chunk2 & 0x000f) * 10;
    let og1add = chunk_og.wrapping_add(0x76767676u32);
    let og2add = chunk2_og.wrapping_add(0x7676u16);
    let result = chunk + (lower_digits + upper_digits) as u32;

    if ((chunk_og & MASK_HI) | (og1add & 0x80808080u32) == 0)
        & ((chunk2_og & MASK_HI2) | (og2add & 0x8080u16) == 0)
    {
        Ok(result) //u16 can guarantee to hold 4 digits
    } else {
        Err(PIE {
            kind: IntErrorKind::InvalidDigit,
        })
    }
}

#[cfg(target_endian = "little")]
#[inline]
pub fn parse_4_chars(s: &[u8]) -> Result<u16, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const ASCII_ZEROS: u32 = 0x30303030u32;

    let chunk1 = unsafe { *(s.as_ptr() as *const u32) ^ ASCII_ZEROS };
    // 1-byte mask trick (works on 4 pairs of single digits)
    let lower_digits = (chunk1 & 0x0f000f00) >> 8; // => 0x00f000f0

    let sum = chunk1.wrapping_add(0x76767676u32) & 0x80808080u32;

    let chunk = lower_digits + ((chunk1 & 0x000f000f) << 3) + ((chunk1 & 0x000f000f) << 1);

    let masked = chunk as u16; // & 0x00ff;
    let cond = (chunk1 & MASK_HI) | sum == 0;

    let m1 = masked << 6;
    let m2 = masked << 5;
    let m3 = masked << 2;

    let r = ((chunk & 0x00ff0000) >> 16) as u16;

    // 2-byte mask trick (works on 2 pairs of two digits)
    let chunk = r + m1 + m2 + m3;

    if cond {
        Ok(chunk) //u16 can guarantee to hold 4 digits
    } else {
        Err(PIE {
            kind: IntErrorKind::InvalidDigit,
        })
    }
}

#[inline]
pub fn parse_2_charsX(s: &[u8]) -> Result<u8, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    const MASK_HI: u16 = 0xf0f0u16;
    const ASCII_ZEROS: u16 = 0x3030u16; //0b0011__0000_0011_0000

    let chunk = unsafe {
        //mask, shift, or
        //   a | b
        // 0x01010101

        // 0b01010101 => 0b001111

        // 04030201 >> 16 = 00000403 |
        // truncate 0201 << 4 = 2010  = 2413

        // 4030201
        //

        // let mut chunk: u16 = 0;
        // std::ptr::copy_nonoverlapping(s.as_ptr() as *const u16, &mut chunk, 1);

        *(s.as_ptr() as *const u16) ^ ASCII_ZEROS
    };
    if (chunk & MASK_HI) | (chunk.wrapping_add(0x7676u16) & 0x8080u16) == 0 {
        // 04030201 >> 16 = 00000403 |
        // truncate 0201 << 4 = 2010  = 2413
        // 4030201
        //
        //
        //
        //
        // let lower_digits = (chunk & 0xf0) >> 8;
        // let upper_digits = (chunk & 0x0f) * 10;
        // let chunk = lower_digits + upper_digits;

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
// #[inline]
// pub fn parse_2_chars(s: &[u8]) -> Result<u8, PIE> {
//     unsafe {
//         let val1 = s.get_unchecked(0) - b'0';
//         let val2 = s.get_unchecked(1) - b'0';
//         if (val1 <= 9) & (val2 <= 9) {
//             Ok(val1 * 10 + val2)
//         } else {
//             Err(PIE {
//                 kind: IntErrorKind::InvalidDigit,
//             })
//         }
//     }
// }

// #[inline]
// pub fn parse_2_charsYY(s: &[u8]) -> Result<(u16), PIE> {
//     //SAFETY:
//     debug_assert!(s.len() >= 2);
//     unsafe {
//         let chunk = *(s.as_ptr() as *const u16) ^ 0x3030u16;
//         let ch = chunk + 0x7676u16;
//    // let upper_digits = (chunk & 0x000f); //as u8;
//             let mut x =   //as u8
//              ((chunk & 0x000f)<<1)
//             + ((chunk & 0x000f) <<3 ) ;
//             let y =((chunk & 0x0f00) >> 8) ;
//             let res = x+y;
//          if (chunk & 0xf0f0u16) | (ch & 0x8080u16) == 0 {//| (chunk + 0x7676u16 & 0x8080u16)
//             // 1-byte mask trick (works on a pair of single digits)
//            // x +=((chunk & 0x0f00) >> 8);
//             Ok(
//                (res)
//             )
//             } else {
//             return Err(PIE {
//                 kind: IntErrorKind::InvalidDigit,
//             });
//         }
//     }
// }

/// Returning u16 rather than u8 as faster.
#[cfg(target_endian = "little")]
#[inline]
pub fn parse_2_chars(s: &[u8]) -> Result<u16, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    unsafe {
        let chunk = *(s.as_ptr() as *const u16) ^ 0x3030u16;
        //Early add
        let ch = chunk.wrapping_add(0x7676u16);
        //Early calc result before use
        let res = ((chunk & 0x000f) << 1) + ((chunk & 0x000f) << 3) + ((chunk & 0x0f00) >> 8);

        if (chunk & 0xf0f0u16) | (ch & 0x8080u16) == 0 {
            //| (chunk + 0x7676u16 & 0x8080u16)
            // 1-byte mask trick (works on a pair of single digits)
            // x +=((chunk & 0x0f00) >> 8);
            Ok(res)
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}

// #[cfg(target_endian = "little")]
// #[inline]
// pub fn parse_2_chars(s: &[u8]) -> Result<u8, PIE> {
//     //SAFETY:
//     debug_assert!(s.len() >= 2);
//     unsafe {
//         let chunk = *(s.as_ptr() as *const u16) ^ 0x3030u16;
//         //Early add
//         let ch = chunk + 0x7676u16;
//         //Early calc result before use (For *10 compiler does *8+*2)
//         let res = (chunk as u8 ) * 10 + (((chunk & 0x0f00) >> 8) as u8);
// //& 0x000f
//         if (chunk & 0xf0f0u16) | (ch & 0x8080u16) == 0 {
//             //| (chunk + 0x7676u16 & 0x8080u16)
//             // 1-byte mask trick (works on a pair of single digits)
//             // x +=((chunk & 0x0f00) >> 8);
//             Ok(res)
//         } else {
//             return Err(PIE {
//                 kind: IntErrorKind::InvalidDigit,
//             });
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use crate::parse::FromStrRadixHelper;

    use super::*;
    use paste::paste;

    macro_rules! gen_tests {
        ($target_type:ty, $min:expr, $max:expr, $step: expr, $max_chars: literal,$postfix: literal, $specific: literal) => {
            paste! {
                #[test]
                fn [<test_ $target_type _specific $postfix>]() {
                    let s = $specific;
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }

                #[cfg(feature="std")]
                #[test]
                fn [<test_invalid_ascii_ $target_type $postfix>]() {
                    for &ascii in [b':', b'/'].iter() {
                        for i in 1..$max_chars {
                            let vec = vec![b'1'; i];
                            for j in 1..i {
                                let mut v = vec.clone();
                                v[j] = ascii;
                                let s = String::from_utf8_lossy(&v[..]);
                                assert_eq!(Err(()), [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "parsing `{}`", s);
                            }
                        }
                    }
                }

                // #[cfg(feature="std")]
                // #[test]
                // fn [<test_invalid_too_big_ $target_type $postfix>]() {
                //     let mut s = ($target_type::MAX as $target_type).to_string();
                //     s.push('1');
                //     assert_eq!(
                //         Err(PIE {
                //             kind: IntErrorKind::PosOverflow
                //         }),
                //         [<parse_ $target_type $postfix>](s.as_bytes()),
                //         " when parsing '{}'",
                //         &s
                //     );
                // }

                // #[test]
                // fn [<test_empty_ $target_type $postfix>]() {
                //     assert_eq!(
                //         Err(PIE {
                //             kind: IntErrorKind::Empty
                //         }),
                //         [<parse_ $target_type $postfix>]("".as_bytes())
                //     );
                // }

                #[cfg(feature="std")]
                #[test]
                fn [<test_ $target_type $postfix>]() {
                    for i in ($min..$max as $target_type).step_by($step) {
                        let s = i.to_string();
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[cfg(feature="std")]
                #[test]
                fn [<test_ $target_type _plus $postfix>]() {
                    for i in ($min..$max as $target_type).step_by($step) {
                        let mut s = i.to_string();
                        s.insert(0, '+');
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[cfg(feature="std")]
                #[test]
                fn [<test_doesnt_accept_plus_after_zero_ $target_type _plus $postfix>]() {
                    let i = $max;
                    let mut s = i.to_string();
                    s.insert(0, '+');
                    for _ in 1..100 {
                        s.insert(0, '0');
                    }
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }

                #[cfg(feature="std")]
                #[test]
                fn [<test_accepts_many_leading_zeros_ $target_type _plus $postfix>]() {
                    let i = $max;
                    let mut s = i.to_string();
                    for _ in 1..100 {
                        s.insert(0, '0');
                    }
                    let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                    assert_eq!(p, [<parse_ $target_type $postfix>](s.as_bytes()).map_err(|_| ()), "fail to parse: '{}'", &s);
                }
            }
        }
    }

    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "", "1");
    gen_tests!(u8, u8::MIN, u8::MAX, 1, 3, "_challenger", "+200");

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

    gen_tests!(
        u64,
        u64::MIN,
        u64::MAX,
        100_301_000_000_000,
        20,
        "",
        "0000000000000000018446744073709551615"
    );
    gen_tests!(
        u64,
        u64::MIN,
        u64::MAX,
        100_301_000_000_000,
        20,
        "_challenger",
        "10000009700000000000"
    );

    gen_tests!(
        i64,
        i64::MIN,
        i64::MAX,
        100_301_000_000_000,
        19,
        "",
        "-999993949854775808"
    );

    gen_tests!(
        i64,
        i64::MIN,
        i64::MAX,
        100_301_000_000_000,
        19,
        "_challenger",
        "1"
    );

    gen_tests!(
        u128,
        u64::MIN as u128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "",
        "10000009700000000000"
    );

    gen_tests!(
        u128,
        u64::MIN as u128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );

    gen_tests!(
        i128,
        u64::MIN as i128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "",
        "1701411834604692317316873037158841057271" // "1:11111111111111"
    );

    gen_tests!(
        i128,
        u64::MIN as i128,
        u64::MAX,
        100_301_000_000_000,
        39,
        "_challenger",
        "123456789012345678901234567890123456789"
    );

    #[test]
    fn test_fuzz1() {
        // needed checked add when checking digits in range.
        check(&[50, 35, 43, 173]);
    }

    #[test]
    fn test_fuzz2() {
        // Too long is defined by std as invalid digit error rather than overflow.
        check(&[48, 48, 54, 54, 49, 54, 56, 57, 54, 49, 51]);
    }

    #[test]
    fn test_fuzz3() {
        //"00661689613" std can deal with any number of leading zeros
        // as it keeps multiplying them by 10...
        check(&[54, 48, 48, 48, 54, 48, 54, 48, 54, 48, 54]);
    }

    #[test]
    fn test_fuzz4() {
        //leading zeros then plus: "0000+6600660"
        check(&[48, 48, 48, 48, 43, 54, 54, 48, 48, 54, 54, 48]);
    }

    #[test]
    fn test_fuzz5() {
        //leading zeros then plus: "0000+6600660"
        check(&[
            43, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
            48, 48, 48, 48, 48, 48,
        ]);
    }
    #[test]
    fn test_fuzz6() {
        check_generic::<u64>(&[
            43, 49, 43, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
        ]);
    }

    fn check(data: &[u8]) {
        if let Ok(s) = String::from_utf8(data.to_vec()) {
            let spec: Result<u32, _> = s.parse();
            let expected = spec.map_err(|e| ());
            assert_eq!(expected, parse_u32(&data).map_err(|e| ()));
            // let expected = spec.map_err(|e| e.kind().clone());
            // assert_eq!(expected, parse_u32(&data).map_err(|e| e.kind));
        } else {
            //just make sure doesn't panic:
            let _ = parse_u32(&data);
        }
    }

    fn check_generic<T>(data: &[u8])
    where
        T: FromStrRadixHelper,
        T: std::str::FromStr,
        T: std::fmt::Debug,
    {
        if let Ok(s) = String::from_utf8(data.to_vec()) {
            let spec: Result<T, _> = s.parse::<T>();
            let expected = spec.map_err(|e| ());
            assert_eq!(expected, parse::<T>(&data).map_err(|e| ()));
            // let expected = spec.map_err(|e| e.kind().clone());
            // assert_eq!(expected, parse_u32(&data).map_err(|e| e.kind));
        } else {
            //just make sure doesn't panic:
            let _ = parse::<T>(&data);
        }
    }
}
