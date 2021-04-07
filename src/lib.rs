//#![feature(unchecked_math)]
use core::arch::x86_64::{
    _mm_cvtsi128_si64, _mm_lddqu_si128, _mm_madd_epi16, _mm_maddubs_epi16, _mm_packus_epi32,
    _mm_set1_epi8, _mm_set_epi16, _mm_set_epi8, _mm_sub_epi16,
};
pub fn std_parse_u64(s: &str) -> u64 {
    s.parse().unwrap()
}

pub fn std_parse_u8(s: &str) -> Result<u8, ()> {
    s.parse().map_err(|_| ())
}

pub fn std_parse_u16(s: &str) -> Result<u16, ()> {
    s.parse().map_err(|_| ())
}

pub fn std_parse_u32(s: &str) -> u32 {
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

// pub fn trick(s: &str) -> u64 {
//     let (upper_digits, lower_digits) = s.split_at(8);
//     parse_8_chars_unchecked(upper_digits) * 100000000 + parse_8_chars_unchecked(lower_digits)
// }

pub fn trick_with_checks(s: &str) -> u64 {
    parse_u64(s).unwrap()
}

/// Parse from "0" to "+255"
pub fn parse_u8(s: &str) -> Result<u8, ()> {
    let mut s = s.as_bytes();
    let first = s.get(0);
    match first {
        Some(val) if *val == b'+' => s = &s[1..],
        Some(val) => {
            if s.len() == 1 {
                let result = val.wrapping_sub(b'0');
                return if result <= 9 { Ok(result) } else { Err(()) };
            }
        }
        _ => {}
    };
    let l = s.len();
    return match l {
        2 => {
            let result = parse_2_chars(s)?;
            Ok(result as u8)
        }
        3 => {
            let val = s[0].wrapping_sub(b'0');
            if val <= 2 {
                match (val * 100).checked_add(parse_2_chars(&s[1..])? as u8) {
                    Some(val) => Ok(val),
                    None => Err(()),
                }
            } else {
                Err(())
            }
        }
        _ => Err(()),
    };
}

pub fn parse_u16(s: &str) -> Result<u16, ()> {
    let mut s = s.as_bytes();
    let l = s.len();
    let first = s.get(0);
    match first {
        Some(val) if *val == b'+' => {
            s = &s[1..];
        }
        Some(val) => {
            if l == 1 {
                let val = val.wrapping_sub(b'0');
                return if val <= 9 {
                    Ok(val as u16)
                } else {
                    return Err(());
                };
            }
        }
        None => return Err(()),
    }

    match l {
        2 => { parse_2_chars(s).map(|val| val as u16) }
        3 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 9 => val as u16,
                _ => return Err(()),
            };
            Ok(val * 100 + parse_2_chars(&s[1..])? as u16)
        }
        4 => {
            parse_4_chars(s).map(|val| val as u16)
        }
        5 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 6 => val as u16  * 10_000,
                _ => return Err(()),
            };
            match val.checked_add(parse_4_chars(&s[1..])? as u16) {
                Some(val) => Ok(val),
                None => return Err(()),
            }
        }
        _ => Err(())
    }
}


//Bit slower odd bit:
// pub fn parse_u16(s: &str) -> Result<u16, ()> {
//     let mut s = s.as_bytes();
//     let l = s.len();
//     let odd: u8 = match s.get(0) {
//         Some(val) => {
//             if *val == b'+' {
//                 s = &s[1..];
//             }
//             let odd = val.wrapping_sub(b'0');
//             if odd > 9 {
//                 return Err(());
//             } else if l == 1 {
//                 return Ok(odd as u16);
//             }
//             odd
//         }
//         None => return Err(()),
//     };

//     match l {
//         2 => { parse_2_chars(s).map(|val| val as u16) }
//         3 => {
//             Ok(odd as u16 * 100 + parse_2_chars(&s[1..])? as u16)
//         }
//         4 => {
//             Ok(parse_2_chars(&s[..2])? * 100 + parse_2_chars(&s[2..])?)
//         }
//         5 => {
//             let val = match (odd as u16).checked_mul(10_000) {
//                 Some(val) => val,
//                 None => return Err(()),
//             };
//             match val.checked_add(parse_4_chars(&s[1..])? as u16) {
//                 Some(val) => Ok(val),
//                 None => return Err(()),
//             }
//         }
//         _ => Err(())
//     }
// }

/// Parses from 0 -> 4_294_967_295 (10 digits and optionally +)
pub fn parse_u32(s: &str) -> Result<u32, ()> {
    let mut s = s.as_bytes();
    let l = s.len();
    match s.get(0) {
        Some(val) if *val == b'+' => {
            s = &s[1..];
        }
        Some(val) => {
            if l == 1 {
                let val = val.wrapping_sub(b'0');
                return if val <= 9 {Ok(val as u32)}
                    else { Err(()) };
            } else if l == 3 {
                let val = val.wrapping_sub(b'0') * 100;
                return Ok((parse_2_chars(&s[1..])? + val as u16) as u32)
            }
        }
        None => return Err(()),
    }
    if l == 2 {
        return parse_2_chars(s).map(|v|v as u32);
    }
    if l >= 8 {
        let mut result = parse_8_chars(&s)?;
        if l == 8 { return Ok(result as u32) }
        
        result *= 10;
        let val = s[8].wrapping_sub(b'0');
        if val > 9 { return Err(()) }
        result += val as u64;
        if l == 9 { return Ok(result as u32) }

        let mut result: u32 = match (result as u32).checked_mul(10) {
            Some(val) => val,
            None => return Err(())
        };
        let val = s[9].wrapping_sub(b'0');
        if val > 9 { return Err(()) }
        result = match result.checked_add(val as u32) {
            Some(val) => val,
            None => return Err(())
        };
        if l == 10 { return Ok(result)}
        return Err(())
    }
    //4,5,6,7
    let mut result = parse_4_chars(s)?;
    if l == 4 {
        return Ok(result);
    }
    if l == 5 {
        result *= 10;
        let val = s[4].wrapping_sub(b'0');
        if val > 9 { return Err(()) }
        return Ok(result + val as u32);
    }
    result *= 100;
    let val = parse_2_chars(&s[4..])?;
    result += val as u32;
    if l == 6 {
        return Ok(result);
    }
    debug_assert_eq!(l, 7);
    result *= 10;
    let val = s[6].wrapping_sub(b'0');
    if val > 9 { return Err(()) }
    return Ok(result + val as u32);


    // let mut slice = s;
    // if slice.len() > 8 {
    //     slice = &s[0..8];
    // }
    // let result = parse_8_chars(&slice)?;
    // if l <= 8 {
    //     return Ok(result as u32);
    // }
    // debug_assert!(result < u32::MAX as u64);
    // let result = result as u32;
    // let rest = parse_4_chars(&s[8..])?;
    // let result = match result.checked_mul(if l < 10 { 10 } else { 100 }) {
    //     Some(val) => val,
    //     None => return Err(()),
    // };
    // match result.checked_add(rest) {
    //     Some(val) => Ok(val),
    //     None => Err(()),
    // }

    // // Consume enough string so rest is a multiple of 4:
    // let unaligned = l % 4;
    // if unaligned > 0 {

    //     s = &s[unaligned..];
    // }
    // while s.len() > 4 {
    //     result = match result.checked_add(parse_4_chars(&s[0..4])?) {
    //         Some(res) => res,
    //         None => return Err(()),
    //     };
    //     result = match result.checked_mul(10_000) {
    //         Some(res) => res,
    //         None => return Err(()),
    //     };
    //     s = &s[4..];
    // }
    // match result.checked_add(parse_4_chars(s)?) {
    //     Some(res) => Ok(res),
    //     None => return Err(()),
    // }
}

// pub fn parse_u32b(s: &str) -> Result<u32, ()> {
//     let result = parse_u64(s)?;
//     result.try_into().map_err(|_| ())
// }

/// Parses 0 to 18_446_744_073_709_551_615
pub fn parse_u64(ss: &str) -> Result<u64, ()> {
    let mut l = ss.len();
    if l < 10 {
        return parse_u32(ss).map(|val| val as u64);
    }
    let mut s = ss.as_bytes();

    match s.get(0) {
        None => return Err(()),
        Some(val) if *val == b'+' => {
            s = &s[1..];
            l -= 1;
        }
        Some(_) => {}
    }

    if l > 20 {
        return Err(());
    }

    let mut result: u64 = 0;
    while l >= 8 {
        result = 100_000_000 * result + parse_8_chars(&s[..8])?;
        s = &s[8..];
        l -= 8;
    }
    if l >= 4 {
        // 20 chars comes here so we need to checked math.
        result = match result.checked_mul(10_000) {
            Some(val) => val,
            None => return Err(())
        };
        result = match result.checked_add(parse_4_chars(&s[..4])? as u64) {
            Some(val) => val,
            None => return Err(())
        };
        s = &s[4..];
        l -= 4;
    }
    if l >= 2 {
        result = result * 100 + parse_2_chars(&s[..2])? as u64;
        s = &s[2..];
        l -= 2;
    }
    if l == 1 {
        let val = s[0].wrapping_sub(b'0');
        if val > 9 { return Err(()) }
        result  = result * 10 + val as u64;
    }
    return Ok(result)
}

// u128: 0 to 340282366920938463463374607431768211455

pub fn trick_with_checks_i64(src: &str) -> i64 {
    parse_signed64(src).unwrap()
}

pub fn parse_signed64(src: &str) -> Result<i64, ()> {
    let (is_positive, digits) = match src.as_bytes().get(0) {
        None => {
            return Err(());
        }
        Some(b'-') => (false, &src[1..]),
        Some(_) => (true, src),
    };
    let i = parse_u64(digits)?;
    if is_positive {
        if i > i64::MAX as u64 {
            Err(())
        } else {
            Ok(i as i64)
        }
    } else {
        // Negative
        if i > i64::MAX as u64 + 1 {
            Err(())
        } else {
            match 0_i64.checked_sub(i as i64) {
                Some(res) => Ok(res),
                None => Err(()),
            }
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

fn parse_8_chars(s: &[u8]) -> Result<u64, ()> {
    let l = s.len();
    debug_assert!(l >= 8);
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const MASK_LOW: u64 = 0x0f0f0f0f0f0f0f0fu64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;
    //let mut chunk = 0;

    let mut chunk:u64 = 0u64;// [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
    //chunk[..l].copy_from_slice(s);
    //let mut chunk = u64::from_ne_bytes(chunk);
    unsafe
    {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u64,
            &mut chunk,
            1//s.len(), //std::mem::size_of_val(&chunk),
        );

        //cast_ref::<[u8; 4], u32> will fail if the reference isn't already aligned to 4).

        // SAFETY: Unknown memory due to < 8 len replaced with with b'0's:
      //  let r = 0x3030303030303030u64.wrapping_shr(l as u32 * 8);
        //chunk = chunk << ((8 - l) * 8) | r;
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

fn parse_2_chars(s: &[u8]) -> Result<u16, ()> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    // let l = s.len();
    const MASK_HI: u16 = 0xf0f0u16;
    const MASK_LOW: u16 = 0x0f0fu16;
    const ASCII_ZEROS: u16 = 0x3030u16;
    // let mut r: [u8;2] = [0,0];
    let mut chunk: u16 = 0;
    // println!("size:{}", std::mem::size_of_val(&s));
    // println!("size:{}", s.len());
    // println!("size:{}", std::mem::size_of_val(&chunk));

    // let mut chars4 : [u8; 4] =[0,0,0,0];// s.try_into().unwrap();//[0,0,0,0];
    //    let r = &mut chunk[..l];
    // let mut r = chunk;
    //r.copy_from_slice(s);
    // for (i, ch) in s.iter().enumerate() {
    //     r[i] = *ch;
    // }
    // unsafe {
    //    std::ptr::copy_nonoverlapping(s.as_ptr() as *const u8, &mut r as *mut u8, l);
    // }
    unsafe {
       
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u16,
            &mut chunk,
            1
            //std::mem::size_of_val(&chunk), //s.len(), //std::mem::size_of_val(&s),
        );

        // std::ptr::copy_nonoverlapping(
        //     s.as_ptr() as *const u8,
        //     (&mut r) as *mut u8,
        //     l//s.len(), //std::mem::size_of_val(&s),
        // );
    }
    // let mut chunk = u16::from_ne_bytes(r);

    // SAFETY: Unknown memory due to < 8 len replaced with with b'0's:
    //chunk = chunk << ((2 - l) * 8) | ASCII_ZEROS.wrapping_shr((l * 8) as u32);

    //println!("size:{}", std::mem::size_of_val(&chunk));
    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let x = chunk & MASK_LOW;
    const RESULT_MASK: u16 = !0u16 / 255 * 128;
    const N: u16 = 9;
    const N_MASK: u16 = !0u16 / 255 * (127 - N);
    if (chunk & MASK_HI - ASCII_ZEROS) + ((x + N_MASK | x) & RESULT_MASK) != 0 {
        return Err(());
    }

    // 1-byte mask trick (works on a pair of single digits)
    let lower_digits = (chunk & 0x0f00) >> 8;
    let upper_digits = (chunk & 0x000f) * 10;
    let chunk = lower_digits + upper_digits;
    Ok(chunk)
}

fn parse_4_chars(s: &[u8]) -> Result<u32, ()> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const MASK_LOW: u32 = 0x0f0f0f0fu32;
    const ASCII_ZEROS: u32 = 0x30303030u32;
   // let mut r: [u8; 4] = [0, 0, 0, 0];
    let mut chunk: u32 = 0;
    // println!("size:{}", std::mem::size_of_val(&s));
    // println!("size:{}", s.len());
    // println!("size:{}", std::mem::size_of_val(&chunk));

    //SAFETY:
    //debug_assert!(s.len() <= 4); //todo make fn unsafe in case of larger inputs?
    // let mut chars4 : [u8; 4] =[0,0,0,0];// s.try_into().unwrap();//[0,0,0,0];
    //    let r = &mut chunk[..l];
    // let mut r = chunk;
    //r.copy_from_slice(s);
    // for (i, ch) in s.iter().enumerate() {
    //     r[i] = *ch;
    // }
    // unsafe {
    //    std::ptr::copy_nonoverlapping(s.as_ptr() as *const u8, &mut r as *mut u8, l);
    // }
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u32,
            &mut chunk,
        1//  std::mem::size_of_val(&chunk)
//            1, //s.len(), //std::mem::size_of_val(&s),
        );

        // std::ptr::copy_nonoverlapping(
        //     s.as_ptr() as *const u8,
        //     (&mut r) as *mut u8,
        //     l//s.len(), //std::mem::size_of_val(&s),
        // );
    }

    //println!("hm");
    //println!("h");
   // let mut chunk = u32::from_ne_bytes(r);

    // SAFETY: Unknown memory due to < 8 len replaced with with b'0's:
  //  chunk = chunk << ((4 - l) * 8) | ASCII_ZEROS.wrapping_shr((l * 8) as u32);

    //println!("size:{}", std::mem::size_of_val(&chunk));
    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let x = chunk & MASK_LOW;
    const RESULT_MASK: u32 = !0u32 / 255 * 128;
    const N: u32 = 9;
    const N_MASK: u32 = !0u32 / 255 * (127 - N);
    if (chunk & MASK_HI - ASCII_ZEROS) + ((x + N_MASK | x) & RESULT_MASK) != 0 {
        return Err(());
    }

    // 1-byte mask trick (works on 4 pairs of single digits)
    let lower_digits = (chunk & 0x0f000f00) >> 8;
    let upper_digits = (chunk & 0x000f000f) * 10;
    let chunk = lower_digits + upper_digits;

    // 2-byte mask trick (works on 2 pairs of two digits)
    let lower_digits = (chunk & 0x00ff0000) >> 16;
    let upper_digits = (chunk & 0x000000ff) * 100;
    let chunk = lower_digits + upper_digits;
    Ok(chunk)
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

// const MULTIPLIER: &[u32] = &[
//     1_000_000_000,
//     100_000_000,
//     10_000_000,
//     1_000_000,
//     100_000,
//     10_000,
//     1_000,
//     100,
//     10,
//     1,
// ];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        assert_eq!(Err(()), parse_u8(""));
        assert_eq!(Err(()), parse_u16(""));
        assert_eq!(Err(()), parse_u32(""));
        assert_eq!(Err(()), parse_u64(""));
    }

    #[test]
    fn test_invalid_ascii_low() {
        assert_eq!(Err(()), parse_u8("1/4"));
        assert_eq!(Err(()), parse_u16("1/4"));
        assert_eq!(Err(()), parse_u32("1/4"));
        assert_eq!(Err(()), parse_u64("1/4"));
    }

    #[test]
    fn test_invalid_ascii_hi() {
        assert_eq!(Err(()), parse_u8("1:4"));
        assert_eq!(Err(()), parse_u16("1:4"));
        assert_eq!(Err(()), parse_u32("1:4"));
        assert_eq!(Err(()), parse_u64("1:4"));
    }

    #[test]
    fn test_invalid_too_big() {
        assert_eq!(Err(()), parse_u8(&(u8::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u16(&(u16::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u32(&(u32::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u64(&(u64::MAX as u128 + 1).to_string()));
    }

    #[test]
    fn test_u8() {
        let mut s = String::new();
        for i in u8::MIN..u8::MAX {
            s.clear();
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u8, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u8(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u16() {
        let mut s = String::new();
        for i in u16::MIN..u16::MAX {
            s.clear();
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u16, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u16(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u32() {
        let mut s = String::new();
        for i in (u32::MIN..u32::MAX).step_by(10_301) {
            s.clear();
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u32, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u32(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u64() {
        let mut s = String::new();
        for i in (u64::MIN..u64::MAX).step_by(10_301_000_000_000) {
            s.clear();
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u64, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u64(&s), "fail to parse: '{}'", &s);
        }
    }
}
