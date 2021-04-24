#![feature(int_error_matching)]
use std::str::FromStr;

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

#[cfg(target_endian = "little")]
#[inline]
pub fn parse_16_chars_og(s: &[u8]) -> Result<u64, PIE> {
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



#[cfg(target_endian = "little")]
#[inline]
pub fn parse_16_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;
    unsafe {
        let chunk = *(s.as_ptr() as *const u128) ^ ASCII_ZEROS;
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

        let chk = chunk_og + 0x76767676767676767676767676767676u128;
        // 8-byte mask trick (works on a pair of eight digits)
        let lower_digits = ((chunk & 0x00000000ffffffff0000000000000000) >> 64) as u64;
        let upper_digits = (chunk as u64 ) * 100_00_00_00;//& 0x00000000ffffffff
        let chunk = lower_digits + upper_digits;

        if (chunk_og & MASK_HI)
            | (chk
                & 0x80808080808080808080808080808080u128)
            == 0
        {
            Ok(chunk) //u64 can guarantee to contain 19 digits.
        } else {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
    }
}


// 2.94, 2.99, 2.91
#[cfg(target_endian = "little")]
#[inline]
pub fn parse_8_chars_orig(s: &[u8]) -> Result<u32, PIE> {
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
            let upper_digits = (chunk & 0x000000000000ffff) * 10000;//10000 = 8192 + 1024 + 512 + 256+ 16
            //8192 + 2048 + 16 - 256
            //16384 - 
            let chunk = lower_digits + upper_digits;
            Ok(chunk as u32) //u32 can guarantee to contain 9 digits.
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

    unsafe {
        let chunk = *(s.as_ptr() as *const u64) ^ ASCII_ZEROS;
        let chunk_og = chunk;
        let chk = chunk_og + 0x7676767676767676u64;
        // 1-byte mask trick (works on 4 pairs of single digits)
        let lower_digits = (chunk & 0x0f000f000f000f00) >> 8;
        let upper_digits = (chunk & 0x000f000f000f000f) * 10;//Compiler does *8 + *2
        let chunk = lower_digits + upper_digits;

        // 2-byte mask trick (works on 2 pairs of two digits)
        let lower_digits = (chunk & 0x00ff000000ff0000) >> 16;
        let upper_digits = (chunk & 0x000000ff000000ff) * 100;
        let chunk = lower_digits + upper_digits;

        // 4-byte mask trick (works on a pair of four digits)
        let lower_digits = ((chunk & 0x0000ffff00000000) >> 32) as u32;
        let upper_digits = (chunk as u32 ) * 10000;//10000 = 8192 + 1024 + 512 + 256+ 16
        //8192 + 2048 + 16 - 256  //& 0x0000ffff

        //We do this before the if shaving 300ps.
        let chunk = lower_digits + upper_digits;

        if (chunk_og & MASK_HI) | (chk & 0x8080808080808080u64) == 0 {
            Ok(chunk) //u32 can guarantee to contain 9 digits.
        } else {
            Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            })
        }
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
    const ASCII_ZEROS2: u16 = 0x3030u16;//0b0011__0000_0011_0000

    unsafe {
        let chunk = *(s.as_ptr() as *const u32);
        let chunk2 = *(s.get_unchecked(4..).as_ptr() as *const u16);


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

        let lower_digits = ((chunk2 & 0x0f00) >> 8);
        let upper_digits = (chunk2 & 0x000f) * 10;
        let og1add = chunk_og + 0x76767676u32;
        let og2add = chunk2_og + 0x7676u16;
        let result = chunk + (lower_digits + upper_digits) as u32;
  
        if ((chunk_og & MASK_HI) | (og1add & 0x80808080u32) == 0) & (
            (chunk2_og & MASK_HI2) | (og2add & 0x8080u16) == 0) {

            Ok(result) //u16 can guarantee to hold 4 digits
        } else {
            Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    }

}

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

#[cfg(target_endian = "little")]
#[inline]
pub fn parse_4_chars_orig(s: &[u8]) -> Result<u16, PIE> {
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
            // 04030201 >> 16 = 00000403 |
            // truncate 0201 << 4 = 2010  = 2413
            // 4030201
            //
            /*
             8 7 6 5 4 3 2 1  => 48372615 => 12345678


             4 3 2 1  => 4231  => 1234

             4231
              42
               31*10

             4   3   2   1
                 4       2
             3*10   1*10

             3*10 4 1*10 2
                    3*10  4
             1*10 2
             (x 100)

             0b0000
             0b1001 9 => 90 == 01011010
                    1 => 10 == 00001010



             1     2     3    4
             x10        x10  x0
             x100 x100       x0
            */

            // 1-byte mask trick (works on 4 pairs of single digits)
            let lower_digits = (chunk & 0x0f000f00) >> 8; // => 0x00f000f0
            let upper_digits = (chunk & 0x000f000f) * 10;
            let chunk = lower_digits + upper_digits;

            // 2-byte mask trick (works on 2 pairs of two digits)
            let lower_digits = ((chunk & 0x00ff0000) >> 16) as u16; // => 0x0000ff00
            let upper_digits = (chunk as u16 & 0x00ff) * 100;
            let chunk = lower_digits + upper_digits;
            Ok(chunk) //u16 can guarantee to hold 4 digits
        } else {
            Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    }
}


#[cfg(target_endian = "little")]
#[inline]
pub fn parse_4_chars(s: &[u8]) -> Result<u16, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const ASCII_ZEROS: u32 = 0x30303030u32;

    unsafe {
        let chunk1 = *(s.as_ptr() as *const u32) ^ ASCII_ZEROS;

        // 1-byte mask trick (works on 4 pairs of single digits)
        let lower_digits = (chunk1 & 0x0f000f00) >> 8; // => 0x00f000f0

        let sum = chunk1 + 0x76767676u32 & 0x80808080u32;

        let chunk = lower_digits + ((chunk1 & 0x000f000f) <<3) + ((chunk1 & 0x000f000f) <<1);

        let masked = (chunk as u16);// & 0x00ff;
        let cond = (chunk1 & MASK_HI) | sum == 0;

        let m1 = (masked << 6);
        let m2 = (masked << 5);
        let m3 = (masked << 2);

        let r = ((chunk & 0x00ff0000) >> 16) as u16;

        // 2-byte mask trick (works on 2 pairs of two digits)
        let chunk = r
        + m1
        + m2
        + m3;

        if cond {
            Ok(chunk) //u16 can guarantee to hold 4 digits
        } else {
            Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    }
}

#[inline]
pub fn parse_2_charsX(s: &[u8]) -> Result<u8, PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    const MASK_HI: u16 = 0xf0f0u16;
    const ASCII_ZEROS: u16 = 0x3030u16; //0b0011__0000_0011_0000

    unsafe {
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

        let chunk = *(s.as_ptr() as *const u16) ^ ASCII_ZEROS;
        if (chunk & MASK_HI) | (chunk + 0x7676u16 & 0x8080u16) == 0 {
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
pub fn parse_2_chars(s: &[u8]) -> Result<(u16), PIE> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    unsafe {
        let chunk = *(s.as_ptr() as *const u16) ^ 0x3030u16;
        //Early add
        let ch = chunk + 0x7676u16;
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
    gen_tests!(
        u64,
        u64::MIN,
        u64::MAX,
        100_301_000_000_000,
        20,
        "_challenger",
        "1"
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
        "+0"
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
        "-170141183460469231731687303715884105728"
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
}
