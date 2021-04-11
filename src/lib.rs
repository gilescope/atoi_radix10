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
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(mut val) => {
            if *val == b'+' {
                match iter.next() {
                    Some(alt_val) => {
                        val = alt_val;
                    }
                    None => return Err(()),
                }
            }
            let val = val.wrapping_sub(b'0');
            match iter.next() {
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 {
                        return Err(());
                    }
                    match iter.next() {
                        Some(val3) => {
                            let val3 = val3.wrapping_sub(b'0');
                            let val2 = val2 * 10;
                            match val {
                                0 => Ok(val2 + val3),
                                1 => Ok(100 + val2 + val3),
                                2 => {
                                    let two = val2 + val3;
                                    if two <= 55 {
                                        Ok(200 + two)
                                    } else {
                                        Err(())
                                    }
                                }
                                _ => Err(()),
                            }
                        }
                        None => {
                            if val <= 9 {
                                Ok(val * 10 + val2)
                            } else {
                                Err(())
                            }
                        }
                    }
                }
                None => {
                    if val <= 9 {
                        Ok(val)
                    } else {
                        Err(())
                    }
                }
            }
        }
        _ => Err(()),
    }
}

/// Parse from "0" to "+255"
pub fn parse_u8_best(s: &str) -> Result<u8, ()> {
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
    let l: usize;
    let first = s.get(0);
    match first {
        Some(mut val) => {
            if *val == b'+' {
                s = &s[1..];
                val = match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
            }
            l = s.len();
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
        2 => parse_2_chars(s).map(|val| val as u16),
        3 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 9 => val as u16,
                _ => return Err(()),
            };
            Ok(val * 100 + parse_2_chars(&s[1..])? as u16)
        }
        4 => parse_4_chars(s),
        5 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 6 => val as u16 * 10_000,
                _ => return Err(()),
            };
            match val.checked_add(parse_4_chars(&s[1..])?) {
                Some(val) => Ok(val),
                None => return Err(()),
            }
        }
        _ => Err(()),
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
pub fn parse_u32_old_best(s: &str) -> Result<u32, ()> {
    let mut s = s.as_bytes();
    match s.get(0) {
        Some(val) if *val == b'+' => {
            s = &s[1..];
            val
        }
        Some(val) => val,
        None => return Err(()),
    };
    if s.len() < 10 {
        let mut result = 0;
        for c in s {
            let val = c.wrapping_sub(b'0');
            if val <= 9 {
                result = result * 10 + val as u32;
            } else {
                return Err(());
            };
        }
        return Ok(result);
    } else {
        let mut result = 0;
        for c in s {
            let val = c.wrapping_sub(b'0');
            if val <= 9 {
                result = result * 10 + val as u32;
            } else {
                return Err(());
            };
        }
        return Ok(result);
    }
}

pub fn parse_u32_best(s: &str) -> Result<u32, ()> {
    let mut s = s.as_bytes();
    let val = match s.get(0) {
        Some(val) => {
            if *val == b'+' {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
            } else {
                val
            }
        }
        None => return Err(()),
    };
    let l = s.len();
    match l {
        1 => {
            let val = val.wrapping_sub(b'0');
            if val <= 9 {
                Ok(val as u32)
            } else {
                Err(())
            }
        }
        2 => {
            let val = val.wrapping_sub(b'0');
            let val2 = s[1].wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) {
                return Err(());
            };
            Ok((val * 10 + val2) as u32)
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = s[1].wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            };
            Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
        }
        4 => Ok(parse_4_chars(s)? as u32),
        5 => {
            let mut result = parse_4_chars(s)? as u32;
            result *= 10;
            let val = s[4].wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            }
            Ok(result + val as u32)
        }
        6 => {
            let mut result = parse_4_chars(s)? as u32;
            result *= 100;
            let val = parse_2_chars(&s[4..])?;
            result += val as u32;
            Ok(result)
        }
        7 => {
            let mut result = parse_4_chars(s)? as u32;
            result *= 100;
            let val = parse_2_chars(&s[4..])?;
            result += val as u32;
            result *= 10;
            let val = s[6].wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            }
            Ok(result + val as u32)
        }
        8 => parse_8_chars(&s),
        9 => {
            let val = val.wrapping_sub(b'0') as u32;
            let result = parse_8_chars(&s[1..])?;
            if val > 9 {
                return Err(());
            }
            Ok(result + (val as u32 * 100_000_000))
        }
        10 => {
            let mut val = val.wrapping_sub(b'0') as u32;
            let mut val2 = s[1].wrapping_sub(b'0') as u32;
            if (val > 4) | (val2 > 9) {
                return Err(());
            }
            let mut result = parse_8_chars(&s[2..])?;
            val *= 1_000_000_000;
            val2 *= 100_000_000;
            result += val;
            match result.checked_add(val2) {
                Some(val) => Ok(val),
                None => Err(()),
            }
        }
        _ => Err(()),
    }
}

pub fn parse_u32(s: &str) -> Result<u32, ()> {
    let mut s = s.as_bytes();
    let (val, val2) = match s.get(0) {
        Some(val) => {
            let val = if *val == b'+' {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
            } else {
                val
            };

            let val2 = match s.get(1) {
                Some(val2) => val2,
                None => {
                    let val = val.wrapping_sub(b'0');
                    return if val <= 9 { Ok(val as u32) } else { Err(()) };
                }
            };

            (val, val2)
        }
        None => return Err(()),
    };
    let l = s.len();
    match l {
        2 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) {
                return Err(());
            };
            Ok((val * 10 + val2) as u32)
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            };
            Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
        }
        4 => Ok(parse_4_chars(s)? as u32),
        5 => {
            let result = parse_4_chars(&s[1..])? as u32;
            let val = val.wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            }
            Ok(result + (val as u32 * 10_000))
        }
        6 => {
            let mut result = parse_4_chars(s)? as u32;
            result *= 100;
            let val = parse_2_chars(&s[4..])?;
            result += val as u32;
            Ok(result)
        }
        7 => {
            let result = parse_4_chars(&s[1..])? as u32;
            let loose_change = parse_2_chars(&s[5..])? as u32;
            let val = val.wrapping_sub(b'0') as u32;
            if val > 9 {
                return Err(());
            }
            Ok(val * 1_000_000 + result * 100 + loose_change)
        }
        8 => parse_8_chars(&s),
        9 => {
            let val = val.wrapping_sub(b'0') as u32;
            let result = parse_8_chars(&s[1..])?;
            if val > 9 {
                return Err(());
            }
            Ok(result + (val as u32 * 100_000_000))
        }
        10 => {
            let mut val = val.wrapping_sub(b'0') as u32;
            let mut val2 = val2.wrapping_sub(b'0') as u32;
            if (val > 4) | (val2 > 9) {
                return Err(());
            }
            let mut result = parse_8_chars(&s[2..])?;
            val *= 1_000_000_000;
            val2 *= 100_000_000;
            result += val;
            match result.checked_add(val2) {
                Some(val) => Ok(val),
                None => Err(()),
            }
        }
        _ => Err(()),
    }
}

/// Parses 0 to 18_446_744_073_709_551_615
pub fn parse_u64(ss: &str) -> Result<u64, ()> {
    let mut s = ss.as_bytes();
    let (val, val2) = match s.get(0) {
        Some(val) => {
            let val = if *val == b'+' {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
            } else {
                val
            };

            let val2 = match s.get(1) {
                Some(val2) => val2,
                None => {
                    let val = val.wrapping_sub(b'0');
                    return if val <= 9 { Ok(val as u64) } else { Err(()) };
                }
            };

            (val, val2)
        }
        None => return Err(()),
    };

    let l = s.len();
    let mut res = 0;
    if l & 2 != 0 {
        let val = val.wrapping_sub(b'0');
        let val2 = val2.wrapping_sub(b'0');
        if (val > 9) | (val2 > 9) {
            return Err(());
        };
        res += (val * 10 + val2) as u64 * TENS_U64[s.len() - 2];

        //res += parse_2_chars(&s)? as u64 * TENS_U64[s.len() - 2];
        s = &s[2..];
    }
    if l & 1 != 0 {
        let val = s[0].wrapping_sub(b'0');
        if val > 9 {
            return Err(());
        };
        res += val as u64 * TENS_U64[s.len() - 1];
        s = &s[1..];
    }
    if l & 16 != 0 {
        if l >= 20 {
            // Treat checked case separately
            if l == 20 {
                let val = val.wrapping_sub(b'0') as u64;
                if val > 1 {
                    return Err(());
                }
                return match (parse_4_chars(&s)? as u64 * 10_000_000_000_000_000)
                    .checked_add(parse_16_chars(&s[4..])? as u64)
                {
                    Some(val) => Ok(val),
                    None => Err(()),
                }
            }
            return Err(());
        }
        res += parse_16_chars(&s)? * TENS_U64[s.len() - 16];//TODO always 1
        s = &s[16..];
    }
    if l & 8 != 0 {
        res += parse_8_chars(&s)? as u64 * TENS_U64[s.len() - 8];
        s = &s[8..];
    }
    if l & 4 != 0 {
        res += parse_4_chars(&s)? as u64 * TENS_U64[s.len() - 4];
        s = &s[4..];
    }
    Ok(res)
}

/// Parses 0 to 18_446_744_073_709_551_615
pub fn parse_u64_best(ss: &str) -> Result<u64, ()> {
    let mut s = ss.as_bytes();
    let (val, val2) = match s.get(0) {
        Some(val) => {
            let val = if *val == b'+' {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
            } else {
                val
            };

            let val2 = match s.get(1) {
                Some(val2) => val2,
                None => {
                    let val = val.wrapping_sub(b'0');
                    return if val <= 9 { Ok(val as u64) } else { Err(()) };
                }
            };

            (val, val2)
        }
        None => return Err(()),
    };
    let l = s.len();
    match l {
        2 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) {
                return Err(());
            };
            Ok((val * 10 + val2) as u64)
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            };
            Ok((val as u16 * 100 + (val2 as u16 * 10 + val3 as u16)) as u64)
        }
        4 => Ok(parse_4_chars(s)? as u64),
        5 => {
            let result = parse_4_chars(&s[1..])? as u32;
            let val = val.wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            }
            Ok((result + (val as u32 * 10_000)) as u64)
        }
        6 => {
            let result = parse_4_chars(s)? as u32;
            let val = parse_2_chars(&s[4..])?;
            Ok((result * 100 + val as u32) as u64)
        }
        7 => {
            let result = parse_4_chars(&s[1..])? as u32;
            let loose_change = parse_2_chars(&s[5..])? as u32;
            let val = val.wrapping_sub(b'0') as u32;
            if val > 9 {
                return Err(());
            }
            Ok((val * 1_000_000 + result * 100 + loose_change) as u64)
        }
        8 => parse_8_chars(&s).map(|val| val as u64),
        9 => {
            let val = val.wrapping_sub(b'0') as u32;
            let result = parse_8_chars(&s[1..])?;
            if val > 9 {
                return Err(());
            }
            Ok((result + (val as u32 * 100_000_000)) as u64)
        }
        10 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) {
                return Err(());
            }
            let result = parse_8_chars(&s[2..])? as u64;
            Ok(val * 1_000_000_000 + val2 * 100_000_000 + result)
        }
        11 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            }
            let result = parse_8_chars(&s[3..])? as u64;
            Ok(val * 10_000_000_000 + val2 * 1_000_000_000 + val3 * 100_000_000 + result)
        }
        12 => Ok(parse_4_chars(s)? as u64 * 1_0000_0000 + parse_8_chars(&s[4..])? as u64),
        13 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val > 9 {
                return Err(());
            }
            Ok(val as u64 * 1_0000_0000_0000
                + parse_4_chars(&s[1..])? as u64 * 1_0000_0000
                + parse_8_chars(&s[5..])? as u64)
        }
        14 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) {
                return Err(());
            }
            Ok(val as u64 * 10_0000_0000_0000
                + val2 as u64 * 1_0000_0000_0000
                + parse_4_chars(&s[2..])? as u64 * 1_0000_0000
                + parse_8_chars(&s[6..])? as u64)
        }
        15 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            }
            Ok(val as u64 * 100_0000_0000_0000
                + val2 as u64 * 10_0000_0000_0000
                + val3 as u64 * 1_0000_0000_0000
                + parse_4_chars(&s[3..])? as u64 * 1_0000_0000
                + parse_8_chars(&s[7..])? as u64)
        }
        16 => parse_16_chars(s),
        17 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val > 9 {
                return Err(());
            }
            Ok(val * 10_000_000_000_000_000 + parse_16_chars(&s[1..])?)
        }
        18 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) {
                return Err(());
            }
            Ok(val * 100_000_000_000_000_000
                + val2 * 10_000_000_000_000_000
                + parse_16_chars(&s[2..])?)
        }
        19 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                return Err(());
            }
            Ok(val * 1_000_000_000_000_000_000
                + val2 * 100_000_000_000_000_000
                + val3 * 10_000_000_000_000_000
                + parse_16_chars(&s[3..])?)
        }
        20 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val > 1 {
                return Err(());
            }
            match (parse_4_chars(&s)? as u64 * 10_000_000_000_000_000)
                .checked_add(parse_16_chars(&s[4..])? as u64)
            {
                Some(val) => Ok(val),
                None => Err(()),
            }
        }
        _ => Err(()),
    }

    // let mut result: u64 = 0;
    // while l >= 8 {
    //     result = 100_000_000 * result + parse_8_chars(&s[..8])? as u64;
    //     s = &s[8..];
    //     l -= 8;
    // }
    // if l >= 4 {
    //     // 20 chars comes here so we need to checked math.
    //     result = match result.checked_mul(10_000) {
    //         Some(val) => val,
    //         None => return Err(()),
    //     };
    //     result = match result.checked_add(parse_4_chars(&s[..4])? as u64) {
    //         Some(val) => val,
    //         None => return Err(()),
    //     };
    //     s = &s[4..];
    //     l -= 4;
    // }
    // if l >= 2 {
    //     result = result * 100 + parse_2_chars(&s[..2])? as u64;
    //     s = &s[2..];
    //     l -= 2;
    // }
    // if l == 1 {
    //     let val = s[0].wrapping_sub(b'0');
    //     if val > 9 {
    //         return Err(());
    //     }
    //     result = result * 10 + val as u64;
    // }
    // return Ok(result);
}

/// Parses 0 to 18_446_744_073_709_551_615
pub fn parse_u64_old_best(ss: &str) -> Result<u64, ()> {
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
        result = 100_000_000 * result + parse_8_chars(&s[..8])? as u64;
        s = &s[8..];
        l -= 8;
    }
    if l >= 4 {
        // 20 chars comes here so we need to checked math.
        result = match result.checked_mul(10_000) {
            Some(val) => val,
            None => return Err(()),
        };
        result = match result.checked_add(parse_4_chars(&s[..4])? as u64) {
            Some(val) => val,
            None => return Err(()),
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
        if val > 9 {
            return Err(());
        }
        result = result * 10 + val as u64;
    }
    return Ok(result);
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

fn parse_16_chars(s: &[u8]) -> Result<u64, ()> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const MASK_LOW: u128 = 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fu128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;

    let mut chunk: u128 = 0u128;
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u128,
            &mut chunk,
            1, //s.len(), //std::mem::size_of_val(&chunk),
        );
        //cast_ref::<[u8; 4], u32> will fail if the reference isn't already aligned to 4).

        // SAFETY: Unknown memory due to < 8 len replaced with with b'0's:
        //  let r = 0x3030303030303030u64.wrapping_shr(l as u32 * 8);
        //chunk = chunk << ((8 - l) * 8) | r;
    }

    // See https://graphics.stanford.edu/~seander/bithacks.html#HasMoreInWord
    let x = chunk & MASK_LOW;
    const RESULT_MASK: u128 = !0u128 / 255 * 128;
    const N: u128 = 9;
    const N_MASK: u128 = !0u128 / 255 * (127 - N);
    if (chunk & MASK_HI) - ASCII_ZEROS | ((x + N_MASK | x) & RESULT_MASK) != 0 {
        // _mm_cmpgt_epi8 would also work nicely here if available on target.
        return Err(());
    }

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
}

fn parse_8_chars(s: &[u8]) -> Result<u32, ()> {
    debug_assert!(s.len() >= 8);
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const MASK_LOW: u64 = 0x0f0f0f0f0f0f0f0fu64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;
    //let mut chunk = 0;

    let mut chunk: u64 = 0u64; // [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
                               //chunk[..l].copy_from_slice(s);
                               //let mut chunk = u64::from_ne_bytes(chunk);
    unsafe {
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u64,
            &mut chunk,
            1, //s.len(), //std::mem::size_of_val(&chunk),
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
    Ok(chunk as u32) //u32 can guarantee to contain 9 digits.
}

fn parse_4_chars(s: &[u8]) -> Result<u16, ()> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const MASK_LOW: u32 = 0x0f0f0f0fu32;
    const ASCII_ZEROS: u32 = 0x30303030u32;
    // let mut r: [u8; 4] = [0, 0, 0, 0];
    let mut chunk: u32 = 0;

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
        std::ptr::copy_nonoverlapping(s.as_ptr() as *const u32, &mut chunk, 1);
    }

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
    Ok(chunk as u16) //u16 can guarantee to hold 4 digits
}

fn parse_2_chars(s: &[u8]) -> Result<u8, ()> {
    //SAFETY:
    debug_assert!(s.len() >= 2);
    const MASK_HI: u16 = 0xf0f0u16;
    const MASK_LOW: u16 = 0x0f0fu16;
    const ASCII_ZEROS: u16 = 0x3030u16;
    let mut chunk: u16 = 0;

    unsafe {
        std::ptr::copy_nonoverlapping(s.as_ptr() as *const u16, &mut chunk, 1);
    }

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
    Ok(chunk as u8) // u8 can guarantee to hold 2 chars.
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

const TENS_U32: &[u32] = &[
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
];

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
    fn test_u32_specific() {
        let s = "100002108";
        let p: Result<u32, ()> = s.parse().map_err(|_| ());
        assert_eq!(p, parse_u32(&s), "fail to parse: '{}'", &s);
    }
    #[test]
    fn test_u64_specific() {
        let s = "100412";
        let p: Result<u64, ()> = s.parse().map_err(|_| ());
        assert_eq!(p, parse_u64(&s), "fail to parse: '{}'", &s);
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

    #[test]
    fn test_u8_plus() {
        let mut s = String::new();
        for i in u8::MIN..u8::MAX {
            s.clear();
            s.push('+');
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u8, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u8(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u16_plus() {
        let mut s = String::new();
        for i in u16::MIN..u16::MAX {
            s.clear();
            s.push('+');
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u16, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u16(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u32_plus() {
        let mut s = String::new();
        for i in (u32::MIN..u32::MAX).step_by(10_301) {
            s.clear();
            s.push('+');
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u32, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u32(&s), "fail to parse: '{}'", &s);
        }
    }

    #[test]
    fn test_u64_plus() {
        let mut s = String::new();
        for i in (u64::MIN..u64::MAX).step_by(10_301_000_000_000) {
            s.clear();
            s.push('+');
            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u64, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u64(&s), "fail to parse: '{}'", &s);
        }
    }
}
