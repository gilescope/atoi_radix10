pub fn std_parse_u8(s: &str) -> Result<u8, ()> {
    s.parse().map_err(|_| ())
}

pub fn std_parse_u16(s: &str) -> Result<u16, ()> {
    s.parse().map_err(|_| ())
}

pub fn std_parse_u32(s: &str) -> u32 {
    s.parse().unwrap()
}

pub fn std_parse_u64(s: &str) -> u64 {
    s.parse().unwrap()
}

pub fn std_parse_u128(s: &str) -> u128 {
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

const PLUS : u8 = b'+'.wrapping_sub(b'0');

/// Parse from "0" to "+255"
pub fn parse_u8(s: &str) -> Result<u8, ()> {
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(val) => {
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == PLUS { // '+' - '0' = 251
                    match iter.next() {
                        Some(alt_val) => {
                            val = alt_val.wrapping_sub(b'0');
                            if val > 9 {
                                return Err(());
                            }
                        }
                        None => return Err(()),
                    }
                }
            }
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
                        None => Ok(val * 10 + val2)
                    }
                }
                None => Ok(val)
            }
        }
        _ => Err(()),
    }
}

/// Parse from "0" to "+255"
pub fn parse_u8_best(s: &str) -> Result<u8, ()> {
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
pub fn parse_u8_old_best(s: &str) -> Result<u8, ()> {
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
    let (val, val2, val3) = match s.get(0) {
        Some(val) => {
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == PLUS {
                    s = &s[1..];
                    val = match s.get(0) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val > 9 { return Err(()) };
                            val
                        },
                        None => return Err(()),
                    }
                } else { return Err(()); }
            }
            let val2 = match s.get(1) {
                None => {
                    return Ok(val as u16);
                },
                Some(val2) => {
                    val2
                }
            };
            let val3 = match s.get(2) {
                None => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 { return Err(()); }
                    return Ok((val * 10 + val2) as u16);
                },
                Some(val3) => {
                    val3
                }
            };
            (val, val2, val3)
        }
        None => return Err(()),
    };
    let l = s.len();
    // 111
    match l {
        3 => {
            let val2 = val2.wrapping_sub(b'0');
            let val3 = val3.wrapping_sub(b'0');
            if (val2 > 9) | (val3 > 9) { return Err(()) }
            Ok(val as u16 * 100 + val2 as u16 * 10 + val3 as u16)
        }
        4 => parse_4_chars(s),
        5 => {
            if val > 6 { return Err(()); }
            match (val as u16 * 10_000).checked_add(parse_4_chars(&s[1..])?) {
                Some(val) => Ok(val),
                None => return Err(()),
            }
        }
        _ => Err(()),
    }
}

pub fn parse_u16_best(s: &str) -> Result<u16, ()> {
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
                Err(())
            } else {
                Ok((val * 10 + val2) as u32)
            }
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = s[1].wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) | (val3 > 9) {
                Err(())
            } else {
                Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
            }
        }
        4 => Ok(parse_4_chars(s)? as u32),
        5 => {
            let mut result = parse_4_chars(s)? as u32;
            result *= 10;
            let val = s[4].wrapping_sub(b'0');
            if val > 9 {
                Err(())
            } else {
                Ok(result + val as u32)
            }
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
    let val = match s.get(0) {
        Some(val) => {
            if *val != b'+' {
                val
            } else {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(()),
                }
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
            if (val <= 9) & (val2 <= 9) {
                Ok((val * 10 + val2) as u32)
            } else {
                Err(())
            }
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = s[1].wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
                Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
            } else {
                Err(())
            }
        }
        4 => Ok(parse_4_chars(s)? as u32),
        5 => {
            let result = parse_4_chars(s)? as u32 * 10;
            let val = s[4].wrapping_sub(b'0');
            if val <= 9 {
                Ok(result + val as u32)
            } else {
                Err(())
            }
        }
        6 => {
            let result = parse_4_chars(s)? as u32 * 100;
            let val = parse_2_chars(&s[4..])?;
            Ok(result + val as u32)
        }
        7 => {
            let mut result = parse_4_chars(s)? as u32 * 100;
            let val = parse_2_chars(&s[4..])?;
            result += val as u32;
            result *= 10;
            let val = s[6].wrapping_sub(b'0');
            if val <= 9 {
                Ok(result + val as u32)
            } else {
                Err(())
            }
        }
        8 => parse_8_chars(&s),
        9 => {
            let val = val.wrapping_sub(b'0') as u32;
            let result = parse_8_chars(&s[1..])?;
            if val <= 9 {
                Ok(result + (val * 100_000_000))
            } else {
                Err(())
            }
        }
        10 => {
            let mut val = val.wrapping_sub(b'0') as u32;
            let mut val2 = s[1].wrapping_sub(b'0') as u32;
            if (val <= 4) & (val2 <= 9) {
                let mut result = parse_8_chars(&s[2..])?;
                val *= 1_000_000_000;
                val2 *= 100_000_000;
                result += val;
                match result.checked_add(val2) {
                    Some(val) => Ok(val),
                    None => Err(()),
                }
            } else {
                return Err(());
            }
        }
        _ => Err(()),
    }
}


// DEAD END: Tried to fold in the check of '+' but not fast enough.
// pub fn parse_u32(s: &str) -> Result<u32, ()> {
//     let s = s.as_bytes();
//     let l = s.len();
//     unsafe {
//     match l {
//         1 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             return if val < 10 {
//                 Ok(val as u32)
//             } else {
//                 Err(())
//             };
//         }
//         2 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//             if (val < 10) & (val2 < 10) {
//                 return Ok((val * 10 + val2) as u32);
//             }
//             if (val == PLUS) & (val2 < 10) {
//                 return Ok(val2 as u32)
//             }
//             return Err(());
//         }
//         3 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//             let val3 = s.get_unchecked(2).wrapping_sub(b'0');
//             if (val < 10 ) & (val2 < 10) & (val3 < 10) {
//                 return Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
//             };
//             if (val == PLUS) & (val2 < 10) & (val3 < 10) {
//                 return Ok((val2 * 10 + val3) as u32);
//             }
//             return Err(());
//         }
//         4 => match parse_4_chars(s) {
//             Ok(val) => return Ok(val as u32),
//             Err(_) => {
//                 let val = s.get_unchecked(0).wrapping_sub(b'0');
//                 let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//                 let val3 = s.get_unchecked(2).wrapping_sub(b'0');
//                 if (val < 10 ) & (val2 < 10) & (val3 < 10) {
//                     return Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
//                 };
//                 return Err(());
//             }
//         }
//         5 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             if val <= 9 {
//                 Ok(val as u32 * 10_000 + parse_4_chars(&s.get_unchecked(1..))? as u32)
//             } else {
//                  if val == PLUS {
//                     return parse_4_chars(&s.get_unchecked(1..)).map(|val| val as u32);
//                 }
//                 Err(())
//             }
//         }
//         6 => {
//             match parse_2_chars(&s) {
//                 Ok(val) => {
//                     let result = parse_4_chars(s.get_unchecked(2..))? as u32;
//                     Ok(result + val as u32 * 10_000)
//                 },
//                 Err(_) => {
//                     let val = s.get_unchecked(0);
//                     if *val == b'+' {
//                         let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//                         if val2 < 10 {
//                             return Ok(val2 as u32 * 10_000 + parse_4_chars(s.get_unchecked(2..))? as u32)
//                         }
//                     }
//                     Err(())
//                 }
//             }
//         }
//         7 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             if val <= 9 {
//                 let result = parse_4_chars(&s.get_unchecked(1..))? as u32 * 100;
//                 let loose_change = parse_2_chars(&s.get_unchecked(5..))? as u32;
//                 Ok(result + loose_change + (val as u32 * 1000_000))
//             } else {
//                 if val == PLUS {
//                     let result = parse_4_chars(&s[1..])? as u32 * 100;
//                     let loose_change = parse_2_chars(&s.get_unchecked(5..))? as u32;
//                     return Ok(result + loose_change)
//                 }
//                 Err(())
//             }
//         }
//         8 => {
//             match parse_8_chars(&s) {
//                 Ok(val) => Ok(val),
//                 Err(_) => {
//                     if *s.get_unchecked(0) == b'+' {
//                         let val = s.get_unchecked(1).wrapping_sub(b'0');
//                         if val <= 9 {
//                             let result = parse_4_chars(&s.get_unchecked(2..))? as u32 * 100;
//                             let loose_change = parse_2_chars(&s.get_unchecked(6..))? as u32;
//                             return Ok((val as u32 * 100_0000) + result + loose_change)
//                         }
//                     }
//                     Err(())
//                 }
//             }
//         },
//         9 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             if val <= 9 {
//                 let result = parse_8_chars(&s.get_unchecked(1..))?;
//                 Ok(val as u32 * 1_0000_0000 + result)
//             } else {
//                 if val == PLUS {
//                     return parse_8_chars(&s.get_unchecked(1..));
//                 }
//                 Err(())
//             }
//         }
//         10 => {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as u32;
//             if (val <= 4) & (val2 <= 9) {
//                 let mut result = parse_8_chars(&s.get_unchecked(2..))?;
//                 let val = val as u32 * 1_000_000_000;
//                 val2 *= 100_000_000;
//                 result += val;
//                 match result.checked_add(val2) {
//                     Some(val) => Ok(val),
//                     None => Err(()),
//                 }
//             } else {
//                 if val == PLUS {
//                     if val2 > 9 {
//                         return Err(());
//                     };
//                     let result = parse_8_chars(&s.get_unchecked(2..))?;
//                     return Ok(val2 as u32 * 1_0000_0000 + result)
//                 }
//                 Err(())
//             }
//         }
//         11 => {
//             if *s.get_unchecked(0) != b'+' {
//                 return Err(())
//             }
//             let s = s.get_unchecked(1..);
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as u32;
//             if (val > 4) | (val2 > 9) {
//                 return Err(());
//             }
//             let mut result = parse_8_chars(&s.get_unchecked(2..))?;
//             let val = val as u32 * 1_000_000_000;
//             val2 *= 100_000_000;
//             result += val;
//             match result.checked_add(val2) {
//                 Some(val) => Ok(val),
//                 None => Err(()),
//             }
//          }
//         _ => Err(()),
//     }
// }
// }

// pub fn parse_u32(s: &str) -> Result<u32, ()> {
//     unsafe {
//         let mut s = s.as_bytes();
//         let (val, val2) = match s.get(0) {
//             Some(val) => {
//                 let val = if *val == b'+' {
//                     s = &s.get_unchecked(1..);
//                     match s.get(0) {
//                         Some(val) => val,
//                         None => return Err(()),
//                     }
//                 } else {
//                     val
//                 };

//                 let val2 = match s.get(1) {
//                     Some(val2) => val2,
//                     None => {
//                         let val = val.wrapping_sub(b'0');
//                         return if val <= 9 { Ok(val as u32) } else { Err(()) };
//                     }
//                 };

//                 (val, val2)
//             }
//             None => return Err(()),
//         };

//         let l = s.len();
//         let mut res = 0;
//         if l >= 10 {
//             if l > 10 {
//                 return Err(());
//             }
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             if (val > 4) | (val2 > 9) {
//                 return Err(());
//             };
//             let val = val as u32 * TENS_U32.get_unchecked(9);
//             let val2 = val2 as u32 * TENS_U32.get_unchecked(8);
//             s = &s.get_unchecked(2..);

//             match val.checked_add(val2 + parse_8_chars(&s)?) {
//                 Some(val) => return Ok(val),
//                 None => return Err(())
//             };
//         }
//         if l & 2 != 0 {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) {
//                 return Err(());
//             };
//             res += val as u32 * TENS_U32.get_unchecked(s.len() - 1)
//                 + val2 as u32 * TENS_U32.get_unchecked(s.len() - 2);
//             s = &s.get_unchecked(2..);
//         }
//         if l & 8 != 0 {
//             let val = parse_8_chars(&s)?;
//             s = &s.get_unchecked(8..);
//             res += val * TENS_U32.get_unchecked(s.len());
//         }
//         if l & 4 != 0 {
//             let val = parse_4_chars(&s)? as u32;
//             s = &s.get_unchecked(4..);
//             res += val * TENS_U32.get_unchecked(s.len());
//         }
//         if l & 1 != 0 {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             if val > 9 {
//                 return Err(());
//             };
//             res += val as u32;
//         }
//         Ok(res)
//     }
// }


pub fn parse_u32_old(s: &str) -> Result<u32, ()> {
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
pub fn parse_u64(s: &str) -> Result<u64, ()> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
                    s = &s.get_unchecked(1..);
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
            res += val as u64 * TENS_U64.get_unchecked(s.len() - 1)
                + val2 as u64 * TENS_U64.get_unchecked(s.len() - 2);
            s = &s.get_unchecked(2..);
        }
        if l & 1 != 0 {
            let val = s.get_unchecked(0).wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            };
            s = &s.get_unchecked(1..);
            res += val as u64 * TENS_U64.get_unchecked(s.len());
        }
        if l & 16 != 0 {
            let val16 = parse_16_chars(&s)?;
            if l >= 20 {
                // Treat checked case separately
                if l == 20 {//TODO what if l & 32 but not 16?
                    let val = match val16.checked_mul(10_000) {
                        Some(val) => val,
                        None => return Err(()),
                    };
                    return match val.checked_add(parse_4_chars(&s[16..])? as u64) {
                        Some(val) => Ok(val),
                        None => Err(()),
                    };
                }
                return Err(());
            }
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U64.get_unchecked(s.len()); //TODO always 1
        }
        if l & 8 != 0 {
            let val = parse_8_chars(&s)? as u64;
            s = &s.get_unchecked(8..);
            res += val * TENS_U64.get_unchecked(s.len());
        }
        if l & 4 != 0 {
            res += parse_4_chars(&s)? as u64;
        }
        Ok(res)
    }
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

/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)
pub fn parse_u128(s: &str) -> Result<u128, ()> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
                    s = &s.get_unchecked(1..);
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
                        return if val <= 9 { Ok(val as u128) } else { Err(()) };
                    }
                };

                (val, val2)
            }
            None => return Err(()),
        };
        let l = s.len();
        if l < 39 {
            let mut res = 0u128;
            if l & 2 != 0 {
                let val = val.wrapping_sub(b'0');
                let val2 = val2.wrapping_sub(b'0');
                if (val <= 9) & (val2 <= 9) {
                    res += val as u128 * TENS_U128.get_unchecked(s.len() - 1)
                    + val2 as u128 * TENS_U128.get_unchecked(s.len() - 2);
                    s = &s.get_unchecked(2..);
                } else {
                    return Err(());
                };
            }
            if l & 1 != 0 {
                let val = s.get_unchecked(0).wrapping_sub(b'0');
                if val <= 9 {
                    s = &s.get_unchecked(1..);
                    res += val as u128 * TENS_U128.get_unchecked(s.len());
                } else {
                    return Err(());
                };
            }
            if l & 16 != 0 {
                let val16 = parse_16_chars(&s)? as u128;
                s = &s.get_unchecked(16..);
                res += val16 * TENS_U128.get_unchecked(s.len());
            }
            if l & 8 != 0 {
                let val = parse_8_chars(&s)? as u128;
                s = &s.get_unchecked(8..);
                res += val * TENS_U128.get_unchecked(s.len());
            }
            if l & 32 != 0 {
                let val16 = parse_16_chars(&s)? as u128;
                s = &s.get_unchecked(16..);
                res += val16 * TENS_U128.get_unchecked(s.len());

                // Do the same thing again as a parse_32_chars fn would need 256bits.
                let val16 = parse_16_chars(&s)? as u128;
                s = &s.get_unchecked(16..);
                res += val16 * TENS_U128.get_unchecked(s.len());
            }
            if l & 4 != 0 {
                res += parse_4_chars(&s)? as u128;
            }

            Ok(res)
        } else {
            if l == 39 {
                //39 = 32 + 4 + 2 + 1
                let val = val.wrapping_sub(b'0');
                if val > 3 { return Err(()) }
                let val = val as u128 * TENS_U128[38];

                let val2 = val2.wrapping_sub(b'0');
                let val3 = s[2].wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    let mut res = val2 as u128 * TENS_U128.get_unchecked(37)
                    + val3 as u128 * TENS_U128.get_unchecked(36);
                    s = &s.get_unchecked(3..);

                    let val16 = parse_16_chars(&s)? as u128;
                    s = &s.get_unchecked(16..);
                    res += val16 * TENS_U128.get_unchecked(20);

                    // Do the same thing again as a parse_32_chars fn would need 256bits.
                    let val16 = parse_16_chars(&s)? as u128;
                    s = &s.get_unchecked(16..);
                    res += val16 * TENS_U128.get_unchecked(4);

                    res += parse_4_chars(&s)? as u128;

                    match val.checked_add(res) {
                        Some(val) => Ok(val),
                        None => Err(()),
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        }
    }
}


/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)
pub fn parse_u128_best(s: &str) -> Result<u128, ()> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
                    s = &s.get_unchecked(1..);
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
                        return if val <= 9 { Ok(val as u128) } else { Err(()) };
                    }
                };

                (val, val2)
            }
            None => return Err(()),
        };

        let l = s.len();
        if l >= 39 {
            if l > 39 {
                return Err(());
            }
            //39 = 32 + 4 + 2 + 1
            let val = val.wrapping_sub(b'0');
            if val > 3 { return Err(()) }
            let val = val as u128 * TENS_U128[38];

            let val2 = val2.wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val2 > 9) | (val3 > 9) {
                return Err(());
            };
            let mut res = val2 as u128 * TENS_U128.get_unchecked(37)
                + val3 as u128 * TENS_U128.get_unchecked(36);
            s = &s.get_unchecked(3..);

            let val16 = parse_16_chars(&s)? as u128;
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U128.get_unchecked(20);

            // Do the same thing again as a parse_32_chars fn would need 256bits.
            let val16 = parse_16_chars(&s)? as u128;
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U128.get_unchecked(4);

            res += parse_4_chars(&s)? as u128;

            return match val.checked_add(res) {
                Some(val) => Ok(val),
                None => Err(()),
            };
        }
        let mut res = 0u128;
        if l & 2 != 0 {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) {
                return Err(());
            };
            res += val as u128 * TENS_U128.get_unchecked(s.len() - 1)
                + val2 as u128 * TENS_U128.get_unchecked(s.len() - 2);
            s = &s.get_unchecked(2..);
        }
        if l & 1 != 0 {
            let val = s.get_unchecked(0).wrapping_sub(b'0');
            if val > 9 {
                return Err(());
            };
            s = &s.get_unchecked(1..);
            res += val as u128 * TENS_U128.get_unchecked(s.len());
        }
        if l & 16 != 0 {
            let val16 = parse_16_chars(&s)? as u128;
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U128.get_unchecked(s.len());
        }
        if l & 8 != 0 {
            let val = parse_8_chars(&s)? as u128;
            s = &s.get_unchecked(8..);
            res += val * TENS_U128.get_unchecked(s.len());
        }
        if l & 32 != 0 {
            let val16 = parse_16_chars(&s)? as u128;
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U128.get_unchecked(s.len());

            // Do the same thing again as a parse_32_chars fn would need 256bits.
            let val16 = parse_16_chars(&s)? as u128;
            s = &s.get_unchecked(16..);
            res += val16 * TENS_U128.get_unchecked(s.len());
        }
        if l & 4 != 0 {
            res += parse_4_chars(&s)? as u128;
        }

        Ok(res)
    }
}

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

#[inline]
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
            1,
        );
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

#[inline]
fn parse_8_chars(s: &[u8]) -> Result<u32, ()> {
    debug_assert!(s.len() >= 8);
    const MASK_HI: u64 = 0xf0f0f0f0f0f0f0f0u64;
    const MASK_LOW: u64 = 0x0f0f0f0f0f0f0f0fu64;
    const ASCII_ZEROS: u64 = 0x3030303030303030u64;

    unsafe {
        let chunk = core::mem::MaybeUninit::<u64>::uninit();
        let mut chunk: u64 = std::mem::transmute(chunk);
        std::ptr::copy_nonoverlapping(
            s.as_ptr() as *const u64,
            &mut chunk,
            1,
        );

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
}

#[inline]
fn parse_4_chars(s: &[u8]) -> Result<u16, ()> {
    //SAFETY:
    debug_assert!(s.len() >= 4);

    const MASK_HI: u32 = 0xf0f0f0f0u32;
    const MASK_LOW: u32 = 0x0f0f0f0fu32;
    const ASCII_ZEROS: u32 = 0x30303030u32;
    let mut chunk: u32 = 0;

    unsafe {
        std::ptr::copy_nonoverlapping(s.as_ptr() as *const u32, &mut chunk, 1);
    }

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

#[inline]
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

    #[test]
    fn test_empty() {
        assert_eq!(Err(()), parse_u8(""));
        assert_eq!(Err(()), parse_u16(""));
        assert_eq!(Err(()), parse_u32(""));
        assert_eq!(Err(()), parse_u64(""));
        assert_eq!(Err(()), parse_u128(""));
    }

    #[test]
    fn test_invalid_ascii_low() {
        assert_eq!(Err(()), parse_u8("1/4"));
        assert_eq!(Err(()), parse_u16("1/4"));
        assert_eq!(Err(()), parse_u32("1/4"));
        assert_eq!(Err(()), parse_u64("1/4"));
        assert_eq!(Err(()), parse_u128("1/4"));
    }

    #[test]
    fn test_invalid_ascii_hi() {
        assert_eq!(Err(()), parse_u8("1:4"));
        assert_eq!(Err(()), parse_u16("1:4"));
        assert_eq!(Err(()), parse_u32("1:4"));
        assert_eq!(Err(()), parse_u64("1:4"));
        assert_eq!(Err(()), parse_u128("1:4"));
    }

    #[test]
    fn test_invalid_too_big() {
        assert_eq!(Err(()), parse_u8(&(u8::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u16(&(u16::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u32(&(u32::MAX as u128 + 1).to_string()));
        assert_eq!(Err(()), parse_u64(&(u64::MAX as u128 + 1).to_string()));

        let mut s = (u128::MAX as u128).to_string();
        s.push('1');
        assert_eq!(Err(()), parse_u128(&s));
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
    fn test_u16_specific() {
        let s = "12";
        let p: Result<u16, ()> = s.parse().map_err(|_| ());
        assert_eq!(p, parse_u16(&s), "fail to parse: '{}'", &s);
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
    fn test_u128_specific() {
        let s = "123456789012345678901234567890123456789";
        let p: Result<u128, ()> = s.parse().map_err(|_| ());
        assert_eq!(p, parse_u128(&s), "fail to parse: '{}'", &s);
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
    fn test_u128() {
     //   let mut s = String::new();
        for i in (u128::MIN..u64::MAX as u128).step_by(usize::MAX) {
   //         s.clear();
            let s = i.to_string();
//            itoa::fmt(&mut s, i).unwrap();
            let p: Result<u128, ()> = s.parse().map_err(|_| ());
            assert_eq!(p, parse_u128(&s), "fail to parse: '{}'", &s);
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
