#![feature(int_error_matching)]
use std::str::FromStr;

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

const PLUS: u8 = b'+'.wrapping_sub(b'0');
const MINUS: u8 = b'-'.wrapping_sub(b'0');

use core::num::IntErrorKind::{self, *};
//use core::num::ParseIntError;
#[derive(Debug, Eq, PartialEq)]
pub struct ParseIntError2 {
    pub kind: IntErrorKind,
}

type PIE = ParseIntError2;

/// Parse from "0" to "+255"
pub fn parse_u8_challenger(s: &str) -> Result<u8, ParseIntError2> {
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(val) => {
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == PLUS {
                    // '+' - '0' = 251
                    match iter.next() {
                        Some(alt_val) => {
                            val = alt_val.wrapping_sub(b'0');
                            if val > 9 {
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            match iter.next() {
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 <= 9 {
                        match iter.next() {
                            Some(val3) => {
                                match iter.next() {
                                    None => {
                                        let val3 = val3.wrapping_sub(b'0');
                                        let val2 = val2 * 10;
                                        if val3 <= 9 {
                                            match val {
                                                1 => Ok(100 + val2 + val3),
                                                2 => {
                                                    let two = val2 + val3;
                                                    if two <= 55 {
                                                        Ok(200 + two)
                                                    } else {
                                                        Err(PIE { kind: PosOverflow })
                                                    }
                                                }
                                                0 => Ok(val2 + val3),
                                                _ => Err(PIE { kind: PosOverflow }),
                                            }
                                        } else {
                                            return Err(PIE { kind: InvalidDigit });
                                        }
                                    },
                                    Some(_) => return Err(PIE { kind: PosOverflow }),
                                }
                            }
                            None => Ok(val * 10 + val2),
                        }
                    } else {
                        return Err(PIE { kind: InvalidDigit });
                    }
                }
                None => Ok(val),
            }
        }
        _ => Err(PIE { kind: Empty }),
    }
}

/// Parse from "0" to "+255"
pub fn parse_u8(s: &str) -> Result<u8, ParseIntError2> {
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(mut val) => {
            if *val == b'+' {
                match iter.next() {
                    Some(alt_val) => {
                        val = alt_val;
                    }
                    None => return Err(PIE { kind: InvalidDigit }),
                }
            }
            let val = val.wrapping_sub(b'0');
            match iter.next() {
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 {
                        return Err(PIE { kind: InvalidDigit });
                    }
                    match iter.next() {
                        Some(val3) => {
                            match iter.next() {
                                None => {
                                    let val3 = val3.wrapping_sub(b'0');
                                    let val2 = val2 * 10;
                                    if val3 <= 9 {
                                        match val {
                                            1 => Ok(100 + val2 + val3),
                                            2 => {
                                                let two = val2 + val3;
                                                if two <= 55 {
                                                    Ok(200 + two)
                                                } else {
                                                    Err(PIE { kind: PosOverflow })
                                                }
                                            }
                                            0 => Ok(val2 + val3),
                                            _ => Err(PIE { kind: PosOverflow }),
                                        }
                                    } else {
                                        return Err(PIE { kind: InvalidDigit });
                                    }
                                },
                                Some(_) => return Err(PIE { kind: PosOverflow }),
                            }
                        }
                        None => {
                            if val <= 9 {
                                Ok(val * 10 + val2)
                            } else {
                                Err(PIE { kind: InvalidDigit })
                            }
                        }
                    }
                }
                None => {
                    if val <= 9 {
                        Ok(val)
                    } else {
                        Err(PIE { kind: InvalidDigit })
                    }
                }
            }
        }
        _ => Err(PIE { kind: Empty }),
    }
}

// /// Parse from "0" to "+255"
// pub fn parse_u8_old_best(s: &str) -> Result<u8, ()> {
//     let mut s = s.as_bytes();
//     let first = s.get(0);
//     match first {
//         Some(val) if *val == b'+' => s = &s[1..],
//         Some(val) => {
//             if s.len() == 1 {
//                 let result = val.wrapping_sub(b'0');
//                 return if result <= 9 { Ok(result) } else { Err(()) };
//             }
//         }
//         _ => {}
//     };
//     let l = s.len();
//     return match l {
//         2 => {
//             let result = parse_2_chars(s)?;
//             Ok(result as u8)
//         }
//         3 => {
//             let val = s[0].wrapping_sub(b'0');
//             if val <= 2 {
//                 match (val * 100).checked_add(parse_2_chars(&s[1..])? as u8) {
//                     Some(val) => Ok(val),
//                     None => Err(()),
//                 }
//             } else {
//                 Err(())
//             }
//         }
//         _ => Err(()),
//     };
// }

pub fn parse_u16(s: &str) -> Result<u16, PIE> {
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
                            if val > 9 {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            };
                            val
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            let val2 = match s.get(1) {
                None => {
                    return Ok(val as u16);
                }
                Some(val2) => val2,
            };
            let val3 = match s.get(2) {
                None => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 {
                        return Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        });
                    }
                    return Ok((val * 10 + val2) as u16);
                }
                Some(val3) => val3,
            };
            (val, val2, val3)
        }
        None => return Err(PIE { kind: Empty }),
    };
    let l = s.len();
    // 111
    match l {
        3 => {
            let val2 = val2.wrapping_sub(b'0');
            let val3 = val3.wrapping_sub(b'0');
            if (val2 > 9) | (val3 > 9) {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
            Ok(val as u16 * 100 + val2 as u16 * 10 + val3 as u16)
        }
        4 => parse_4_chars(s),
        5 => {
            if val > 6 {
                return Err(PIE { kind: PosOverflow });
            }
            match (val as u16 * 10_000).checked_add(parse_4_chars(&s[1..])?) {
                Some(val) => Ok(val),
                None => return Err(PIE { kind: PosOverflow }),
            }
        }
        _ => Err(PIE { kind: PosOverflow }),
    }
}

pub fn parse_u16_challenger(s: &str) -> Result<u16, PIE> {
    let mut s = s.as_bytes();
    let l: usize;
    let first = s.get(0);
    match first {
        Some(mut val) => {
            if *val == b'+' {
                s = &s[1..];
                val = match s.get(0) {
                    Some(val) => val,
                    None => return Err(PIE { kind: InvalidDigit }),
                }
            }
            l = s.len();
            if l == 1 {
                let val = val.wrapping_sub(b'0');
                return if val <= 9 {
                    Ok(val as u16)
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                };
            }
        }
        None => return Err(PIE { kind: Empty }),
    }

    match l {
        2 => parse_2_chars(s).map(|val| val as u16),
        3 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 9 => val as u16,
                _ => {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            };
            Ok(val * 100 + parse_2_chars(&s[1..])? as u16)
        }
        4 => parse_4_chars(s),
        5 => {
            let val = match s.get(0).map(|v| v.wrapping_sub(b'0')) {
                Some(val) if val <= 6 => val as u16 * 10_000,
                _ => return Err(PIE { kind: PosOverflow }),
            };
            match val.checked_add(parse_4_chars(&s[1..])?) {
                Some(val) => Ok(val),
                None => return Err(PIE { kind: PosOverflow }),
            }
        }
        _ => Err(PIE { kind: PosOverflow }),
    }
}

// /// Parses from 0 -> 4_294_967_295 (10 digits and optionally +)
// pub fn parse_u32_old_best(s: &str) -> Result<u32, ()> {
//     let mut s = s.as_bytes();
//     match s.get(0) {
//         Some(val) if *val == b'+' => {
//             s = &s[1..];
//             val
//         }
//         Some(val) => val,
//         None => return Err(()),
//     };
//     if s.len() < 10 {
//         let mut result = 0;
//         for c in s {
//             let val = c.wrapping_sub(b'0');
//             if val <= 9 {
//                 result = result * 10 + val as u32;
//             } else {
//                 return Err(());
//             };
//         }
//         return Ok(result);
//     } else {
//         let mut result = 0;
//         for c in s {
//             let val = c.wrapping_sub(b'0');
//             if val <= 9 {
//                 result = result * 10 + val as u32;
//             } else {
//                 return Err(());
//             };
//         }
//         return Ok(result);
//     }
// }

// pub fn parse_u32_best_15_apr_2021(s: &str) -> Result<u32, ()> {
//     let mut s = s.as_bytes();
//     let val = match s.get(0) {
//         Some(val) => {
//             if *val == b'+' {
//                 s = &s[1..];
//                 match s.get(0) {
//                     Some(val) => val,
//                     None => return Err(()),
//                 }
//             } else {
//                 val
//             }
//         }
//         None => return Err(()),
//     };
//     let l = s.len();
//     match l {
//         1 => {
//             let val = val.wrapping_sub(b'0');
//             if val <= 9 {
//                 Ok(val as u32)
//             } else {
//                 Err(())
//             }
//         }
//         2 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = s[1].wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) {
//                 Err(())
//             } else {
//                 Ok((val * 10 + val2) as u32)
//             }
//         }
//         3 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = s[1].wrapping_sub(b'0');
//             let val3 = s[2].wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) | (val3 > 9) {
//                 Err(())
//             } else {
//                 Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
//             }
//         }
//         4 => Ok(parse_4_chars(s)? as u32),
//         5 => {
//             let mut result = parse_4_chars(s)? as u32;
//             result *= 10;
//             let val = s[4].wrapping_sub(b'0');
//             if val > 9 {
//                 Err(())
//             } else {
//                 Ok(result + val as u32)
//             }
//         }
//         6 => {
//             let mut result = parse_4_chars(s)? as u32;
//             result *= 100;
//             let val = parse_2_chars(&s[4..])?;
//             result += val as u32;
//             Ok(result)
//         }
//         7 => {
//             let mut result = parse_4_chars(s)? as u32;
//             result *= 100;
//             let val = parse_2_chars(&s[4..])?;
//             result += val as u32;
//             result *= 10;
//             let val = s[6].wrapping_sub(b'0');
//             if val > 9 {
//                 return Err(());
//             }
//             Ok(result + val as u32)
//         }
//         8 => parse_8_chars(&s),
//         9 => {
//             let val = val.wrapping_sub(b'0') as u32;
//             let result = parse_8_chars(&s[1..])?;
//             if val > 9 {
//                 return Err(());
//             }
//             Ok(result + (val as u32 * 100_000_000))
//         }
//         10 => {
//             let mut val = val.wrapping_sub(b'0') as u32;
//             let mut val2 = s[1].wrapping_sub(b'0') as u32;
//             if (val > 4) | (val2 > 9) {
//                 return Err(());
//             }
//             let mut result = parse_8_chars(&s[2..])?;
//             val *= 1_000_000_000;
//             val2 *= 100_000_000;
//             result += val;
//             match result.checked_add(val2) {
//                 Some(val) => Ok(val),
//                 None => Err(()),
//             }
//         }
//         _ => Err(()),
//     }
// }

// pub fn parse_u32_challengerXX(s: &str) -> Result<u32, PIE> {
//     let mut s = s.as_bytes();
//     let mut l = s.len();
//     let val = match s.get(0) {
//         Some(val) => {
//             if *val != b'+' {
//                 if l == 1 {
//                     let val = val.wrapping_sub(b'0');
//                     return if val <= 9 {
//                         Ok(val as u32)
//                     } else {
//                         Err(PIE {
//                             kind: IntErrorKind::InvalidDigit,
//                         })
//                     }
//                 }
//                 val
//             } else {
//                 s = &s[1..];
//                 match s.get(0) {
//                     Some(val) => {
//                         l -= 1;
//                         if l == 1 {
//                             let val = val.wrapping_sub(b'0');
//                             return if val <= 9 {
//                                 Ok(val as u32)
//                             } else {
//                                 Err(PIE {
//                                     kind: IntErrorKind::InvalidDigit,
//                                 })
//                             }
//                         }
//                         val
//                     },
//                     None => return Err(PIE { kind: InvalidDigit }),
//                 }
//             }
//         }
//         None => return Err(PIE { kind: Empty }),
//     };
//     match l {
//         // 1 => {
//         //     let val = val.wrapping_sub(b'0');
//         //     if val <= 9 {
//         //         Ok(val as u32)
//         //     } else {
//         //         Err(PIE {
//         //             kind: IntErrorKind::InvalidDigit,
//         //         })
//         //     }
//         // }
//         2 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = s[1].wrapping_sub(b'0');
//             if (val <= 9) & (val2 <= 9) {
//                 Ok((val * 10 + val2) as u32)
//             } else {
//                 Err(PIE {
//                     kind: IntErrorKind::InvalidDigit,
//                 })
//             }
//         }
//         3 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = s[1].wrapping_sub(b'0');
//             let val3 = s[2].wrapping_sub(b'0');
//             if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
//                 Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
//             } else {
//                 Err(PIE {
//                     kind: IntErrorKind::InvalidDigit,
//                 })
//             }
//         }
//         4 => Ok(parse_4_chars(s)? as u32),
//         5 => {
//             let val = val.wrapping_sub(b'0');
//             if val <= 9 {
//                 Ok(val as u32 * 1_0000 + parse_4_chars(&s[1..])? as u32)
//             } else {
//                 Err(PIE {
//                     kind: IntErrorKind::InvalidDigit,
//                 })
//             }
//         }
//         6 => {
//             // let result = parse_4_chars(s)? as u32 * 100;
//             // let val = parse_2_chars(&s[4..])?;
//             parse_6_chars(s)
//         }
//         7 => {
//             let result = parse_6_chars(&s[1..])?;//parse_4_chars(s)? as u32 * 100;
// //            let val = parse_2_chars(&s[4..])?;
//             let val = val.wrapping_sub(b'0');
//             // result += val as u32;
//             // result *= 10;
//             // let val = s[6].wrapping_sub(b'0');
//             if val <= 9 {
//                 Ok((val as u32) * 1000_000 + result)
//             } else {
//                 Err(PIE {
//                     kind: IntErrorKind::InvalidDigit,
//                 })
//             }
//         }
//         8 => parse_8_chars(&s),
//         9 => {
//             let val = val.wrapping_sub(b'0') as u32;
//             let result = parse_8_chars(&s[1..])?;
//             if val <= 9 {
//                 Ok(result + (val * 100_000_000))
//             } else {
//                 Err(PIE {
//                     kind: IntErrorKind::InvalidDigit,
//                 })
//             }
//         }
//         10 => {
//             let mut val = val.wrapping_sub(b'0') as u32;
//             let mut val2 = s[1].wrapping_sub(b'0') as u32;
//             if (val <= 4) & (val2 <= 9) {
//                 let mut result = parse_8_chars(&s[2..])?;
//                 val *= 1_000_000_000;
//                 val2 *= 100_000_000;
//                 result += val;
//                 match result.checked_add(val2) {
//                     Some(val) => Ok(val),
//                     None => Err(PIE { kind: PosOverflow }),
//                 }
//             } else {
//                 return Err(PIE { kind: PosOverflow });
//             }
//         }
//         _ => Err(PIE { kind: PosOverflow }),
//     }
// }

/// Parses from 0 -> 4_294_967_295 (10 digits and optionally +)
pub fn parse_u32(s: &str) -> Result<u32, PIE> {
    let mut s = s.as_bytes();
    let val = match s.get(0) {
        Some(val) => {
            let val = val.wrapping_sub(b'0');
            if val <= 9 {
                val
            } else {
                if val == PLUS {
                    s = &s[1..];
                    match s.get(0) {
                        Some(val2) => {
                            let val2 = (*val2).wrapping_sub(b'0');
                            if val2 <= 9 {
                                val2
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                }
            }
        }
        None => return Err(PIE { kind: Empty }),
    };
    let l = s.len();
    unsafe {
        match l {
            1 => Ok(val as u32),
            2 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    Ok((val * 10 + val2) as u32)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            3 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            4 => Ok(parse_4_chars(s)? as u32),
            5 => Ok(val as u32 * 1_0000 + parse_4_chars(&s[1..])? as u32),
            6 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    let result = parse_4_chars(&s[2..])? as u32;
                    Ok(val as u32 * 10_0000 + val2 as u32 * 1_0000 + result)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            7 => {
                let val2 = parse_4_chars(&s[1..])? as u32 * 100;
                let val3 = parse_2_chars(&s[5..])? as u32;
                Ok(val as u32 * 1_000_000 + val2 + val3)
            }
            8 => parse_8_chars(&s),
            9 => {
                let result = parse_8_chars(&s[1..])?;
                Ok(result + (val as u32 * 100_000_000))
            }
            10 => {
                let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as u32;
                if (val <= 4) & (val2 <= 9) {
                    let mut result = parse_8_chars(&s[2..])?;
                    let val = val as u32 * 1_000_000_000;
                    val2 *= 100_000_000;
                    result += val;
                    match result.checked_add(val2) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    }
                } else {
                    return Err(PIE { kind: PosOverflow });
                }
            }
            _ => Err(PIE { kind: PosOverflow }),
        }
    }
}


/// Parses from 0 -> 4_294_967_295 (10 digits and optionally +)
pub fn parse_u32_challenger(s: &str) -> Result<u32, PIE> {
    let mut s = s.as_bytes();
    let val = match s.get(0) {
        Some(val) => {
            let val = val.wrapping_sub(b'0');
            if val <= 9 {
                val
            } else {
                if val == PLUS {
                    s = &s[1..];
                    match s.get(0) {
                        Some(val2) => {
                            let val2 = (*val2).wrapping_sub(b'0');
                            if val2 <= 9 {
                                val2
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                }
            }
        }
        None => return Err(PIE { kind: Empty }),
    };
    let l = s.len();
    unsafe {
        match l {
            1 => Ok(val as u32),
            2 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    Ok((val * 10 + val2) as u32)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            3 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            4 => Ok(parse_4_chars(s)? as u32),
            5 => Ok(val as u32 * 1_0000 + parse_4_chars(&s[1..])? as u32),
            6 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    let result = parse_4_chars(&s[2..])? as u32;
                    Ok(val as u32 * 10_0000 + val2 as u32 * 1_0000 + result)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            7 => {
                let val2 = parse_4_chars(&s[1..])? as u32 * 100;
                //let val3 = parse_2_chars(&s[5..])? as u32;
                let val3 = s.get_unchecked(5).wrapping_sub(b'0');
                let val4 = s.get_unchecked(6).wrapping_sub(b'0');
                if (val3 <= 9) & (val4 <= 9) {
                    Ok(val as u32 * 1_000_000 + val2 + (val3 * 10) as u32 + val4 as u32)
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            }
            8 => parse_8_chars(&s),
            9 => {
                parse_8_chars(&s[1..]).map(|val2| (val as u32 * 100_000_000) + val2)
  //              let result = parse_8_chars(&s[1..])?;
//                Ok(result + (val as u32 * 100_000_000))
            }
            10 => {
                let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as u32;
                if (val <= 4) & (val2 <= 9) {
                    let mut result = parse_8_chars(&s[2..])?;
                    let val = val as u32 * 1_000_000_000;
                    val2 *= 100_000_000;
                    result += val;
                    match result.checked_add(val2) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    }
                } else {
                    return Err(PIE { kind: PosOverflow });
                }
            }
            _ => Err(PIE { kind: PosOverflow }),
        }
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

// pub fn parse_u32_old(s: &str) -> Result<u32, PIE> {
//     let mut s = s.as_bytes();
//     let (val, val2) = match s.get(0) {
//         Some(val) => {
//             let val = if *val == b'+' {
//                 s = &s[1..];
//                 match s.get(0) {
//                     Some(val) => val,
//                     None => return Err(()),
//                 }
//             } else {
//                 val
//             };

//             let val2 = match s.get(1) {
//                 Some(val2) => val2,
//                 None => {
//                     let val = val.wrapping_sub(b'0');
//                     return if val <= 9 { Ok(val as u32) } else { Err(()) };
//                 }
//             };

//             (val, val2)
//         }
//         None => return Err(()),
//     };
//     let l = s.len();
//     match l {
//         2 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) {
//                 return Err(());
//             };
//             Ok((val * 10 + val2) as u32)
//         }
//         3 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             let val3 = s[2].wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) | (val3 > 9) {
//                 return Err(());
//             };
//             Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
//         }
//         4 => Ok(parse_4_chars(s)? as u32),
//         5 => {
//             let result = parse_4_chars(&s[1..])? as u32;
//             let val = val.wrapping_sub(b'0');
//             if val > 9 {
//                 return Err(());
//             }
//             Ok(result + (val as u32 * 10_000))
//         }
//         6 => {
//             let mut result = parse_4_chars(s)? as u32;
//             result *= 100;
//             let val = parse_2_chars(&s[4..])?;
//             result += val as u32;
//             Ok(result)
//         }
//         7 => {
//             let result = parse_4_chars(&s[1..])? as u32;
//             let loose_change = parse_2_chars(&s[5..])? as u32;
//             let val = val.wrapping_sub(b'0') as u32;
//             if val > 9 {
//                 return Err(());
//             }
//             Ok(val * 1_000_000 + result * 100 + loose_change)
//         }
//         8 => parse_8_chars(&s),
//         9 => {
//             let val = val.wrapping_sub(b'0') as u32;
//             let result = parse_8_chars(&s[1..])?;
//             if val > 9 {
//                 return Err(());
//             }
//             Ok(result + (val as u32 * 100_000_000))
//         }
//         10 => {
//             let mut val = val.wrapping_sub(b'0') as u32;
//             let mut val2 = val2.wrapping_sub(b'0') as u32;
//             if (val > 4) | (val2 > 9) {
//                 return Err(());
//             }
//             let mut result = parse_8_chars(&s[2..])?;
//             val *= 1_000_000_000;
//             val2 *= 100_000_000;
//             result += val;
//             match result.checked_add(val2) {
//                 Some(val) => Ok(val),
//                 None => Err(()),
//             }
//         }
//         _ => Err(()),
//     }
// }

/// Parses 0 to 18_446_744_073_709_551_615
pub fn parse_u64_challenger(s: &str) -> Result<u64, PIE> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
                    s = &s.get_unchecked(1..);
                    match s.get(0) {
                        Some(val) => val,
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    val
                };

                let val2 = match s.get(1) {
                    Some(val2) => val2,
                    None => {
                        let val = val.wrapping_sub(b'0');
                        return if val <= 9 {
                            Ok(val as u64)
                        } else {
                            Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        };
                    }
                };

                (val, val2)
            }
            None => return Err(PIE { kind: Empty }),
        };

        let l = s.len();
        let mut res = 0;
        if l & 2 != 0 {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            if (val > 9) | (val2 > 9) {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            };
            res += val as u64 * TENS_U64.get_unchecked(s.len() - 1)
                + val2 as u64 * TENS_U64.get_unchecked(s.len() - 2);
            s = &s.get_unchecked(2..);
        }
        if l & 1 != 0 {
            let val = s.get_unchecked(0).wrapping_sub(b'0');
            if val > 9 {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            };
            s = &s.get_unchecked(1..);
            res += val as u64 * TENS_U64.get_unchecked(s.len());
        }
        if l & 16 != 0 {
            let val16 = parse_16_chars(&s)?;
            if l >= 20 {
                // Treat checked case separately
                if l == 20 {
                    //TODO what if l & 32 but not 16?
                    let val = match val16.checked_mul(10_000) {
                        Some(val) => val,
                        None => return Err(PIE { kind: PosOverflow }),
                    };
                    return match val.checked_add(parse_4_chars(&s[16..])? as u64) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    };
                }
                return Err(PIE { kind: PosOverflow });
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

/// Parses 0 to 18_446_744_073_709_551_615 (up to 20 chars)
pub fn parse_u64(ss: &str) -> Result<u64, PIE> {
    let mut s = ss.as_bytes();
    let (val, val2) = match s.get(0) {
        Some(val) => {
            let val = if *val == b'+' {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => val,
                    None => return Err(PIE { kind: InvalidDigit }),
                }
            } else {
                val
            };

            let val2 = match s.get(1) {
                Some(val2) => val2,
                None => {
                    let val = val.wrapping_sub(b'0');
                    return if val <= 9 {
                        Ok(val as u64)
                    } else {
                        Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        })
                    };
                }
            };

            (val, val2)
        }
        None => return Err(PIE { kind: Empty }),
    };
    let l = s.len();
    match l {
        2 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            if (val <= 9) & (val2 <= 9) {
                return Ok((val * 10 + val2) as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            };
        }
        3 => {
            let val = val.wrapping_sub(b'0');
            let val2 = val2.wrapping_sub(b'0');
            let val3 = s[2].wrapping_sub(b'0');
            if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
                return Ok((val as u16 * 100 + (val2 as u16 * 10 + val3 as u16)) as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            };
        }
        4 => Ok(parse_4_chars(s)? as u64),
        5 => {
            let result = parse_4_chars(&s[1..])? as u32;
            let val = val.wrapping_sub(b'0');
            if val <= 9 {
                return Ok((result + (val as u32 * 10_000)) as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
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
            if val <= 9 {
                return Ok((val * 1_000_000 + result * 100 + loose_change) as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        8 => parse_8_chars(&s).map(|val| val as u64),
        9 => {
            let val = val.wrapping_sub(b'0') as u32;
            let result = parse_8_chars(&s[1..])?;
            if val <= 9 {
                return Ok((result + (val as u32 * 100_000_000)) as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        10 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) {
                let result = parse_8_chars(&s[2..])? as u64;
                return Ok(val * 1_000_000_000 + val2 * 100_000_000 + result)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        11 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
                let result = parse_8_chars(&s[3..])? as u64;
                return Ok(val * 10_000_000_000 + val2 * 1_000_000_000 + val3 * 100_000_000 + result)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        12 => return Ok(parse_4_chars(s)? as u64 * 1_0000_0000 + parse_8_chars(&s[4..])? as u64),
        13 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val <= 9 {
                return Ok(val as u64 * 1_0000_0000_0000
                    + parse_4_chars(&s[1..])? as u64 * 1_0000_0000
                    + parse_8_chars(&s[5..])? as u64)
            } else { 
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        14 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) {
                return Ok(val as u64 * 10_0000_0000_0000
                    + val2 as u64 * 1_0000_0000_0000
                    + parse_4_chars(&s[2..])? as u64 * 1_0000_0000
                    + parse_8_chars(&s[6..])? as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        15 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
                return Ok(val as u64 * 100_0000_0000_0000
                    + val2 as u64 * 10_0000_0000_0000
                    + val3 as u64 * 1_0000_0000_0000
                    + parse_4_chars(&s[3..])? as u64 * 1_0000_0000
                    + parse_8_chars(&s[7..])? as u64)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        16 => parse_16_chars(s),
        17 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val <= 9 {
                return Ok(val * 10_000_000_000_000_000 + parse_16_chars(&s[1..])?)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        18 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) {
                return Ok(val * 100_000_000_000_000_000
                    + val2 * 10_000_000_000_000_000
                    + parse_16_chars(&s[2..])?)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        19 => {
            let val = val.wrapping_sub(b'0') as u64;
            let val2 = val2.wrapping_sub(b'0') as u64;
            let val3 = s[2].wrapping_sub(b'0') as u64;
            if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
                return Ok(val * 1_000_000_000_000_000_000
                    + val2 * 100_000_000_000_000_000
                    + val3 * 10_000_000_000_000_000
                    + parse_16_chars(&s[3..])?)
            } else {
                return Err(PIE {
                    kind: IntErrorKind::InvalidDigit,
                });
            }
        }
        20 => {
            let val = val.wrapping_sub(b'0') as u64;
            if val <= 1 {
                match (parse_4_chars(&s)? as u64 * 10_000_000_000_000_000)
                .checked_add(parse_16_chars(&s[4..])? as u64)
                {
                    Some(val) => return Ok(val),
                    None => return Err(PIE { kind: PosOverflow }),
                }
            }
            return Err(PIE { kind: PosOverflow });
        }
        _ => Err(PIE { kind: PosOverflow }),
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
// pub fn parse_u64_old_best(ss: &str) -> Result<u64, ()> {
//     let mut l = ss.len();
//     if l < 10 {
//         return parse_u32(ss).map(|val| val as u64);
//     }
//     let mut s = ss.as_bytes();

//     match s.get(0) {
//         None => return Err(()),
//         Some(val) if *val == b'+' => {
//             s = &s[1..];
//             l -= 1;
//         }
//         Some(_) => {}
//     }

//     if l > 20 {
//         return Err(());
//     }

//     let mut result: u64 = 0;
//     while l >= 8 {
//         result = 100_000_000 * result + parse_8_chars(&s[..8])? as u64;
//         s = &s[8..];
//         l -= 8;
//     }
//     if l >= 4 {
//         // 20 chars comes here so we need to checked math.
//         result = match result.checked_mul(10_000) {
//             Some(val) => val,
//             None => return Err(()),
//         };
//         result = match result.checked_add(parse_4_chars(&s[..4])? as u64) {
//             Some(val) => val,
//             None => return Err(()),
//         };
//         s = &s[4..];
//         l -= 4;
//     }
//     if l >= 2 {
//         result = result * 100 + parse_2_chars(&s[..2])? as u64;
//         s = &s[2..];
//         l -= 2;
//     }
//     if l == 1 {
//         let val = s[0].wrapping_sub(b'0');
//         if val > 9 {
//             return Err(());
//         }
//         result = result * 10 + val as u64;
//     }
//     return Ok(result);
// }

/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)

pub fn parse_u128_challenger(s: &str) -> Result<u128, PIE> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
                    s = &s.get_unchecked(1..);
                    match s.get(0) {
                        Some(val) => val,
                        None => {
                            return Err(PIE {
                                kind: IntErrorKind::Empty,
                            })
                        }
                    }
                } else {
                    val
                };

                let val2 = match s.get(1) {
                    Some(val2) => val2,
                    None => {
                        let val = val.wrapping_sub(b'0');
                        return if val <= 9 {
                            Ok(val as u128)
                        } else {
                            Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        };
                    }
                };

                (val, val2)
            }
            None => return Err(PIE { kind: Empty }),
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
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                };
            }
            if l & 1 != 0 {
                let val = s.get_unchecked(0).wrapping_sub(b'0');
                if val <= 9 {
                    s = &s.get_unchecked(1..);
                    res += val as u128 * TENS_U128.get_unchecked(s.len());
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
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
                if val > 3 {
                    return Err(PIE { kind: PosOverflow });
                }
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
                        None => Err(PIE { kind: PosOverflow }),
                    }
                } else {
                    Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            } else {
                Err(PIE { kind: PosOverflow })
            }
        }
    }
}


/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)
pub fn parse_u128(s: &str) -> Result<u128, PIE> {
    unsafe {
        let mut s = s.as_bytes();
        let mut l: usize = s.len();

        let val = match s.get(0) {
            Some(val) => {
                let val = val.wrapping_sub(b'0');
                if val <= 9 {
                    if l == 1 {
                        return Ok(val as u128)
                    }
                    val
                } else {
                    if val == PLUS {
                        s = &s[1..];
                        let val = s[0].wrapping_sub(b'0');
                        if val <= 9 {
                            l -= 1;
                            if l == 1 {
                                return Ok(val as u128)
                            }
                            val
                        } else {
                            return Err(PIE { kind: InvalidDigit });
                        }
                    } else { return Err(PIE { kind: InvalidDigit })}
                }
            }
            None => return Err(PIE { kind: Empty }),
        };

        if l < 39 {
            let mut res = 0u128;
            if l & 1 != 0 {
                s = &s.get_unchecked(1..);
                res += val as u128 * TENS_U128.get_unchecked(s.len());
            }
            if l & 2 != 0 {
                let val = s.get_unchecked(0).wrapping_sub(b'0');
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if (val > 9) | (val2 > 9) {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                };
                res += val as u128 * TENS_U128.get_unchecked(s.len() - 1)
                    + val2 as u128 * TENS_U128.get_unchecked(s.len() - 2);
                s = &s.get_unchecked(2..);
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
                if val <= 3 {
                    let val = val as u128 * TENS_U128[38];

                    let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                    let val3 = s.get_unchecked(2).wrapping_sub(b'0');
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
        
                        return match val.checked_add(res) {
                            Some(val) => Ok(val),
                            None => Err(PIE { kind: PosOverflow }),
                        };
                    } else{
                        return Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        });
                    };
                } else {
                    return Err(PIE { kind: PosOverflow });
                }
            } else {
                return Err(PIE { kind: PosOverflow });
            }
        }
    }
}

pub fn trick_with_checks_i64(src: &str) -> i64 {
    parse_i64(src).unwrap()
}

pub fn parse_i8(s: &str) -> Result<i8, PIE> {
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(val) => {
            if *val == b'-' {
                return match iter.next() {
                    Some(val) => {
                        let val = val.wrapping_sub(b'0');
                        if val <= 9 {
                            match iter.next() {
                                None => Ok(-(val as i8)),
                                Some(val2) => {
                                    let val2 = val2.wrapping_sub(b'0');
                                    if val2 <= 9 {
                                        match iter.next() {
                                            None => Ok(-((val * 10 + val2) as i8)),
                                            Some(val3) => {
                                                match iter.next() {
                                                    None => {
                                                        let val3 = val3.wrapping_sub(b'0');
                                                        if (val3 <= 9) & (val <= 1) {
                                                            let result = val * 100 + val2 * 10 + val3;
                                                            if result < 128 {
                                                                Ok(-(result as i8))
                                                            } else if result == 128 {
                                                                Ok(i8::MIN)
                                                            } else {
                                                                Err(PIE { kind: NegOverflow })
                                                            }
                                                        } else {
                                                            Err(PIE { kind: NegOverflow })
                                                        }
                                                    },
                                                    Some(_) => return Err(PIE { kind: PosOverflow }),
                                                }
                                            }
                                        }
                                    } else {
                                        Err(PIE {
                                            kind: IntErrorKind::InvalidDigit,
                                        })
                                    }
                                }
                            }
                        } else {
                            Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        }
                    }
                    _ => Err(PIE { kind: InvalidDigit }),
                };
            }
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == PLUS {
                    val = match iter.next() {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val <= 9 {
                                val
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                }
            }
            match iter.next() {
                None => Ok(val as i8),
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 <= 9 {
                        match iter.next() {
                            None => Ok((val * 10 + val2) as i8),
                            Some(val3) => {
                                match iter.next() {
                                    None => {
                                        let val3 = val3.wrapping_sub(b'0');
                                        if (val3 <= 9) & (val <= 1) {
                                            let result = val * 100 + val2 * 10 + val3;
                                            if result < 128 {
                                                Ok(result as i8)
                                            } else {
                                                Err(PIE { kind: PosOverflow })
                                            }
                                        } else {
                                            return Err(PIE { kind: PosOverflow });
                                        }
                                    }
                                    Some(_) => return Err(PIE { kind: PosOverflow }),
                                }
                            }
                        }
                    } else {
                        return Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        });
                    }
                }
            }
        }
        _ => Err(PIE { kind: Empty }),
    }
}

// pub fn parse_i8_old_old(s: &str) -> Result<i8, ()> {
//     let mut is_positive = 1;
//     let mut iter = s.as_bytes().iter();
//     match iter.next() {
//         Some(mut val) => {
//             if *val == b'-' {
//                 is_positive = -1;
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             } else if *val == b'+' {
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             }
//             let val = val.wrapping_sub(b'0');
//             match iter.next() {
//                 None => {
//                     if val <= 9 {
//                         Ok(is_positive * val as i8)
//                     } else {
//                         Err(())
//                     }
//                 },
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 <= 9 {
//                         match iter.next() {
//                             None => {
//                                 if val <= 9 {
//                                     Ok(is_positive * (val * 10 + val2) as i8)
//                                 } else {
//                                     Err(())
//                                 }
//                             }
//                             Some(val3) => {
//                                 let val3 = val3.wrapping_sub(b'0');
//                                 let val2 = val2 * 10;
//                                 if (val3 <= 9) & (val <= 1) {
//                                     let result = val * 100 + val2 + val3;
//                                     if result < 128 {
//                                         Ok(is_positive * (result as i8))
//                                     } else if result == 128 && is_positive == -1 {
//                                         Ok(i8::MIN)
//                                     } else {
//                                         Err(())
//                                     }
//                                     // match val {
//                                     //     1 => {
//                                     //         let result = 100 + val2 + val3;
//                                     //         if result < 128 {
//                                     //             Ok(is_positive * (result as i8))
//                                     //         } else if result == 128 && is_positive == -1 {
//                                     //             Ok(i8::MIN)
//                                     //         } else {
//                                     //             Err(())
//                                     //         }
//                                     //     },
//                                     //     0 => {
//                                     //         Ok(is_positive * ((val2 + val3) as i8))
//                                     //     },
//                                     //     _ => Err(()),
//                                     // }
//                                 } else { return Err(()) }
//                             }
//                         }
//                     } else {return Err(());}
//                 }
//             }
//         }
//         _ => Err(()),
//     }
// }

pub fn parse_i8_challenger(s: &str) -> Result<i8, PIE> {
    let mut iter = s.as_bytes().iter();
    match iter.next() {
        Some(mut val) => {
            if *val == b'-' {
                return match iter.next() {
                    Some(val) => {
                        let val = val.wrapping_sub(b'0');
                        if val <= 9 {
                            match iter.next() {
                                None => Ok(-(val as i8)),
                                Some(val2) => {
                                    let val2 = val2.wrapping_sub(b'0');
                                    if val2 <= 9 {
                                        match iter.next() {
                                            None => Ok(-((val * 10 + val2) as i8)),
                                            Some(val3) => {
                                                match iter.next() {
                                                None => {
                                                let val3 = val3.wrapping_sub(b'0');
                                                if (val3 <= 9) & (val <= 1) {
                                                    let result = val * 100 + val2 * 10 + val3;
                                                    if result < 128 {
                                                        Ok(-(result as i8))
                                                    } else if result == 128 {
                                                        Ok(i8::MIN)
                                                    } else {
                                                        Err(PIE { kind: PosOverflow })
                                                    }
                                                } else {
                                                    Err(PIE { kind: PosOverflow })
                                                }
                                            },
                                                Some(_) => return Err(PIE { kind: PosOverflow }),
                                        }
                                            }
                                        }
                                    } else {
                                        Err(PIE {
                                            kind: IntErrorKind::InvalidDigit,
                                        })
                                    }
                                }
                            }
                        } else {
                            Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        }
                    }
                    _ => Err(PIE { kind: InvalidDigit }),
                };
            } else if *val == b'+' {
                match iter.next() {
                    Some(alt_val) => {
                        val = alt_val;
                    }
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        })
                    }
                }
            }
            let val = val.wrapping_sub(b'0');
            match iter.next() {
                None => {
                    if val <= 9 {
                        Ok(val as i8)
                    } else {
                        Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        })
                    }
                }
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 <= 9 {
                        match iter.next() {
                            None => {
                                if val <= 9 {
                                    Ok((val * 10 + val2) as i8)
                                } else {
                                    Err(PIE {
                                        kind: IntErrorKind::InvalidDigit,
                                    })
                                }
                            }
                            Some(val3) => {
                                match iter.next() {
                                    None => {
                                        let val3 = val3.wrapping_sub(b'0');
                                        let val2 = val2 * 10;
                                        if (val3 <= 9) & (val <= 1) {
                                            let result = val * 100 + val2 + val3;
                                            if result < 128 {
                                                Ok(result as i8)
                                            } else {
                                                Err(PIE { kind: PosOverflow })
                                            }
                                        } else {
                                            return Err(PIE { kind: PosOverflow });
                                        }
                                    }
                                    Some(_) => return Err(PIE { kind: PosOverflow }),
                                }
                                    
                            }
                        }
                    } else {
                        return Err(PIE { kind: InvalidDigit });
                    }
                }
            }
        }
        _ => Err(PIE { kind: Empty }),
    }
}

// pub fn parse_i8_old_best(s: &str) -> Result<i8, ()> {
//     let mut is_positive = 1;
//     let mut iter = s.as_bytes().iter();
//     match iter.next() {
//         Some(mut val) => {
//             if *val == b'-' {
//                 is_positive = -1;
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             } else if *val == b'+' {
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             }
//             let val = val.wrapping_sub(b'0');
//             match iter.next() {
//                 None => {
//                     if val <= 9 {
//                         Ok(is_positive * val as i8)
//                     } else {
//                         Err(())
//                     }
//                 },
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 <= 9 {
//                         match iter.next() {
//                             None => {
//                                 if val <= 9 {
//                                     Ok(is_positive * (val * 10 + val2) as i8)
//                                 } else {
//                                     Err(())
//                                 }
//                             }
//                             Some(val3) => {
//                                 let val3 = val3.wrapping_sub(b'0');
//                                 let val2 = val2 * 10;
//                                 if val3 <= 9 {
//                                       match val {
//                                         1 => {
//                                             let result = 100 + val2 + val3;
//                                             if result < 128 {
//                                                 Ok(is_positive * (result as i8))
//                                             } else if result == 128 && is_positive == -1 {
//                                                 Ok(i8::MIN)
//                                             } else {
//                                                 Err(())
//                                             }
//                                         },
//                                         0 => {
//                                             Ok(is_positive * ((val2 + val3) as i8))
//                                         },
//                                         _ => Err(()),
//                                     }
//                                 } else { return Err(()) }
//                             }
//                         }
//                     } else {return Err(());}
//                 }
//             }
//         }
//         _ => Err(()),
//     }
// }

// pub fn parse_i8_best_old1(s: &str) -> Result<i8, ()> {
//     let mut is_positive = 1;//tODO try * -1 / 1
//     let mut iter = s.as_bytes().iter();
//     match iter.next() {
//         Some(mut val) => {
//             if *val == b'+' {
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             } else if *val == b'-' {
//                 is_positive = -1;
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             }
//             let val = val.wrapping_sub(b'0');
//             match iter.next() {
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 > 9 {
//                         return Err(());
//                     }
//                     match iter.next() {
//                         Some(val3) => {
//                             let val3 = val3.wrapping_sub(b'0');
//                             let val2 = val2 * 10;
//                             match val {
//                                 1 => {
//                                     let result = 100 + val2 + val3;
//                                     if is_positive == 1 {
//                                         if result <= i8::MAX as u8 {
//                                             Ok(result as i8)
//                                         } else {
//                                             Err(())
//                                         }
//                                     } else {
//                                         if result <= 128 {
//                                             Ok(-(result as i8))
//                                         } else {
//                                             Err(())
//                                         }
//                                     }
//                                 },
//                                 0 => {
//                                     Ok(is_positive * ((val2 + val3) as i8))
//                                 },
//                                 _ => Err(()),
//                             }
//                         }
//                         None => {
//                             if val <= 9 {
//                                 Ok(is_positive * (val * 10 + val2) as i8)
//                             } else {
//                                 Err(())
//                             }
//                         }
//                     }
//                 }
//                 None => {
//                     if val <= 9 {
//                         Ok(is_positive * val as i8)
//                     } else {
//                         Err(())
//                     }
//                 }
//             }
//         }
//         _ => Err(()),
//     }
// }

// pub fn parse_i8_best_old(src: &str) -> Result<i8, ()> {
//     let (is_positive, digits) = match src.as_bytes().get(0) {
//         None => {
//             return Err(());
//         }
//         Some(b'-') => (false, &src[1..]),
//         Some(_) => (true, src),
//     };
//     let i = parse_u8(digits)?;
//     if is_positive {
//         if i > i8::MAX as u8 {
//             Err(())
//         } else {
//             Ok(i as i8)
//         }
//     } else {
//         // Negative
//         if i > i8::MAX as u8 + 1 {
//             Err(())
//         } else {
//             match 0_i8.checked_sub(i as i8) {
//                 Some(res) => Ok(res),
//                 None => Err(()),
//             }
//         }
//     }
// }

// pub fn parse_i16(s: &str) -> Result<i16, ()> {
//     let mut is_positive = 1;
//     let mut s = s.as_bytes();
//     let (val, val2, val3) = match s.get(0) {
//         Some(val) => {
//             let mut val = val.wrapping_sub(b'0');
//             if val > 9 {
//                 if val == MINUS {
//                     is_positive = -1;
//                     s = &s[1..];
//                     val = match s.get(0) {
//                         Some(val) => {
//                             let val = val.wrapping_sub(b'0');
//                             if val > 9 { return Err(()) };
//                             val
//                         },
//                         None => return Err(()),
//                     }
//                 } else if val == PLUS {
//                     s = &s[1..];
//                     val = match s.get(0) {
//                         Some(val) => {
//                             let val = val.wrapping_sub(b'0');
//                             if val > 9 { return Err(()) };
//                             val
//                         },
//                         None => return Err(()),
//                     }
//                 } else { return Err(()); }
//             }
//             let val2 = match s.get(1) {
//                 None => {
//                     return Ok(is_positive * val as i16);
//                 },
//                 Some(val2) => {
//                     val2
//                 }
//             };
//             let val3 = match s.get(2) {
//                 None => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 > 9 { return Err(()); }
//                     return Ok(is_positive * (val * 10 + val2) as i16);
//                 },
//                 Some(val3) => {
//                     val3
//                 }
//             };
//             (val, val2, val3)
//         }
//         None => return Err(()),
//     };
//     let l = s.len();
//     match l {
//         3 => {
//             let val2 = val2.wrapping_sub(b'0');
//             let val3 = val3.wrapping_sub(b'0');
//             if (val2 > 9) | (val3 > 9) { return Err(()) }
//             Ok(is_positive * val as i16 * 100 + val2 as i16 * 10 + val3 as i16)
//         }
//         4 => parse_4_chars(s).map(|val| is_positive * val as i16),
//         5 => {
//             if val > 3 { return Err(()); }
//             let result = val as u16 * 10_000 + parse_4_chars(&s[1..])?;
//             if result <= 32767 {
//                 Ok(is_positive * result as i16)
//             }
//             else if result == 32768 && is_positive == -1 {
//                 Ok(i16::MIN)
//             } else {
//                 return Err(());
//             }
//         }
//         _ => Err(()),
//     }
// }

pub fn parse_i16(s: &str) -> Result<i16, PIE> {
    let mut s = s.as_bytes();
    match s.get(0) {
        Some(val) => {
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == MINUS {
                    s = &s[1..];
                    val = match s.get(0) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val > 9 {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            };
                            val
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    };
                    let val2 = match s.get(1) {
                        None => {
                            return Ok(-(val as i16));
                        }
                        Some(val2) => val2,
                    };
                    let l = s.len();
                    return match l {
                        2 => {
                            let val2 = val2.wrapping_sub(b'0');
                            if val2 <= 9 {
                                return Ok(val as i16 * -10 - val2 as i16);
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        3 => {
                            let val2 = val2.wrapping_sub(b'0');
                            let val3 = s[2].wrapping_sub(b'0');
                            if (val2 <= 9) & (val3 <= 9) {
                                Ok(val as i16 * -100 + val2 as i16 * -10 - val3 as i16)
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        4 => parse_4_chars(s).map(|val| -(val as i16)),
                        5 => {
                            if val <= 3 {
                                let result = val as u16 * 10_000 + parse_4_chars(&s[1..])?;
                                if result <= 32767 {
                                    Ok(-(result as i16))
                                } else if result == 32768 {
                                    Ok(i16::MIN)
                                } else {
                                    return Err(PIE { kind: PosOverflow });
                                }
                            } else {
                                return Err(PIE { kind: PosOverflow });
                            }
                        }
                        _ => Err(PIE { kind: PosOverflow }),
                    };
                } else if val == PLUS {
                    s = &s[1..];
                    val = match s.get(0) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val > 9 {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            };
                            val
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            let val2 = match s.get(1) {
                None => {
                    return Ok(val as i16);
                }
                Some(val2) => val2,
            };

            let l = s.len();
            match l {
                2 => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 <= 9 {
                        return Ok((val * 10 + val2) as i16);
                    } else {
                        return Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        });
                    }
                }
                3 => {
                    let val2 = val2.wrapping_sub(b'0');
                    let val3 = s[2].wrapping_sub(b'0');
                    if (val2 <= 9) & (val3 <= 9) {
                        Ok(val as i16 * 100 + val2 as i16 * 10 + val3 as i16)
                    } else {
                        Err(PIE {
                            kind: IntErrorKind::InvalidDigit,
                        })
                    }
                }
                4 => parse_4_chars(s).map(|val| val as i16),
                5 => {
                    if val <= 3 {
                        let result = val as u16 * 10_000 + parse_4_chars(&s[1..])?;
                        if result <= 32767 {
                            Ok(result as i16)
                        } else {
                            Err(PIE { kind: PosOverflow })
                        }
                    } else {
                        Err(PIE { kind: PosOverflow })
                    }
                }
                _ => Err(PIE { kind: PosOverflow }),
            }
        }
        None => return Err(PIE { kind: Empty }),
    }
}

pub fn parse_i16_challenger(s: &str) -> Result<i16, PIE> {
    let mut s = s.as_bytes();
    let mut l = s.len();
    match s.get(0) {
        Some(val) => {
            let mut val = val.wrapping_sub(b'0');
            if val > 9 {
                if val == MINUS {
                    val = match s.get(1) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val <= 9 {
                                if l != 2 {
                                    val
                                } else { return Ok(-(val as i16))}
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            }
                        }
                        None => {
                            return Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        }
                    };
                    unsafe {
                        return match l {
                            3 => {
                                let val2 = s.get_unchecked(2);
                                let val2 = val2.wrapping_sub(b'0');
                                if val2 <= 9 {
                                    return Ok(-((val * 10 + val2) as i16));
                                } else {
                                    return Err(PIE {
                                        kind: IntErrorKind::InvalidDigit,
                                    });
                                }
                            }
                            4 => {
                                let val2 = s.get_unchecked(2);
                                let val3 = s.get_unchecked(3);
                                let val2 = val2.wrapping_sub(b'0');
                                let val3 = val3.wrapping_sub(b'0');
                                if (val2 <= 9) & (val3 <= 9) {
                                    Ok(-(val as i16 * 100 + val2 as i16 * 10 + val3 as i16))
                                } else {
                                    return Err(PIE {
                                        kind: IntErrorKind::InvalidDigit,
                                    });
                                }
                            }
                            5 => parse_4_chars(&s.get_unchecked(1..)).map(|val| -(val as i16)),
                            6 => {
                                if val <= 3 {
                                    let result = val as u16 * 10_000 + parse_4_chars(&s.get_unchecked(2..))?;
                                    if result <= 32767 {
                                        Ok(-(result as i16))
                                    } else if result == 32768 {
                                        Ok(i16::MIN)
                                    } else {
                                        return Err(PIE { kind: NegOverflow });
                                    }
                                } else {
                                    return Err(PIE { kind: NegOverflow });
                                }
                            }
                            _ => Err(PIE { kind: NegOverflow }),
                        };
                    }
                } else if val == PLUS {
                    s = &s[1..];
                    l -= 1;
                    val = match s.get(0) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val > 9 {
                                return Err(PIE {
                                    kind: IntErrorKind::InvalidDigit,
                                });
                            };
                            val
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE {
                        kind: IntErrorKind::InvalidDigit,
                    });
                }
            }
            if l == 1 {
                    return Ok(val as i16);
            };
            match l {
              //  1 => { return Ok(val as i16); }
                2 => {
                    unsafe {
                        let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                        if val2 <= 9 {
                            return Ok((val * 10 + val2) as i16);
                        } else {
                            return Err(PIE { kind: InvalidDigit });
                        }
                    }
                }
                3 => {
                    unsafe {
                        let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                        let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                        if (val2 <= 9) & (val3 <= 9) {
                            Ok(val as i16 * 100 + val2 as i16 * 10 + val3 as i16)
                        } else {
                            Err(PIE {
                                kind: IntErrorKind::InvalidDigit,
                            })
                        }
                    }
                }
                4 => {
                //    Ok(0)
                    parse_4_chars(s).map(|val| val as i16)
                },
                5 => {
                    if val <= 3 {
                        let result = val as u16 * 10_000 + parse_4_chars(&s[1..])?;
                        if result <= 32767 {
                            Ok(result as i16)
                        } else {
                            Err(PIE { kind: PosOverflow })
                        }
                    } else {
                        Err(PIE { kind: PosOverflow })
                    }
                }
                _ => Err(PIE {
                    kind: IntErrorKind::PosOverflow,
                }),
            }
        }
        None => return Err(PIE { kind: Empty }),
    }
}

// pub fn parse_i16_old_best(s: &str) -> Result<i16, ()> {
//     let mut is_positive = 1_i16;
//     let mut iter = s.as_bytes().iter();
//     match iter.next() {
//         Some(mut val) => {
//             if *val == b'-' {
//                 is_positive = -1;
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             } else if *val == b'+' {
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(()),
//                 }
//             }
//             let val = val.wrapping_sub(b'0');
//             match iter.next() {
//                 None => {
//                     if val <= 9 {
//                         Ok(is_positive * val as i16)
//                     } else {
//                         Err(())
//                     }
//                 },
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val <= 9 && val2 <= 9 {
//                         match iter.next() {
//                             None => {
//                                 if val <= 9 {
//                                     Ok(is_positive * (val * 10 + val2) as i16)
//                                 } else {
//                                     Err(())
//                                 }
//                             }
//                             Some(val3) => {
//                                 let val3 = val3.wrapping_sub(b'0');
//                                 if val3 <= 9 {
//                                     match iter.next() {
//                                         None => {
//                                             let result = val as i16 * 100 + val2 as i16 * 10 + val3 as i16;
//                                             Ok(is_positive * result)
//                                         }
//                                         Some(val4) => {
//                                             let val4 = val4.wrapping_sub(b'0');
//                                             if val4 <= 9 {
//                                                 match iter.next() {
//                                                     None => {
//                                                         let result = val as i16 * 1000 + val2 as i16 * 100 + val3 as i16 * 10 + val4 as i16;
//                                                         Ok(is_positive * result)
//                                                     }
//                                                     Some(val5) => {
//                                                         match iter.next() {
//                                                             None => {
//                                                                 let val5 = val5.wrapping_sub(b'0');

//                                                                 if val5 <= 9 && val <= 3 {
//                                                                     let result = 10_000 * val as u16
//                                                                                     + 1000 * val2 as u16
//                                                                                     + 100 * val3 as u16 + val4 as u16 * 10 + val5 as u16;
//                                                                     if result <= 32767 {
//                                                                         Ok(is_positive * result as i16)
//                                                                     }
//                                                                     else if result == 32768 && is_positive == -1 {
//                                                                         Ok(i16::MIN)
//                                                                     } else {
//                                                                         return Err(());
//                                                                     }
//                                                                 } else {return Err(())}
//                                                             }
//                                                             Some(_too_many_digits) => { Err(()) }
//                                                         }
//                                                     }
//                                                 }
//                                             } else { return Err(()) }
//                                         }
//                                     }
//                                 } else { return Err(()) }
//                             }
//                         }
//                     } else {return Err(());}
//                 }
//             }
//         }
//         _ => Err(()),
//     }
// }

pub fn parse_i64(src: &str) -> Result<i64, PIE> {
    let (is_positive, digits) = match src.as_bytes().get(0) {
        None => {
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
        Some(b'-') => (false, &src[1..]),
        Some(_) => (true, src),
    };
    let i = parse_u64(digits)?;
    if is_positive {
        if i > i64::MAX as u64 {
            Err(PIE { kind: PosOverflow })
        } else {
            Ok(i as i64)
        }
    } else {
        // Negative
        if i > i64::MAX as u64 + 1 {
            Err(PIE { kind: NegOverflow })
        } else {
            match 0_i64.checked_sub(i as i64) {
                Some(res) => Ok(res),
                None => Err(PIE { kind: NegOverflow }),
            }
        }
    }
}

#[inline]
fn parse_16_chars(s: &[u8]) -> Result<u64, PIE> {
    debug_assert!(s.len() >= 16);
    const MASK_HI: u128 = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0u128;
    const ASCII_ZEROS: u128 = 0x30303030303030303030303030303030u128;

    //let mut chunk: u128 = 0u128;
    unsafe {
        //std::ptr::copy_nonoverlapping(s.as_ptr() as *const u128, &mut chunk, 1);
    
        let chunk = *(s.as_ptr() as *const u128) ^ ASCII_ZEROS;
        if (chunk & MASK_HI) | (chunk + 0x76767676767676767676767676767676u128 & 0x80808080808080808080808080808080u128) == 0 {
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
    const ASCII_ZEROS: u16 = 0x3030u16;//0b0011__0000_0011_0000

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
        ($target_type:ty, $max:expr, $step: expr, $max_chars: literal,$postfix: literal, $specific: literal) => {
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
                    for i in ($target_type::MIN..$max as $target_type).step_by($step) {
                        let s = i.to_string();
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }

                #[test]
                fn [<test_ $target_type _plus $postfix>]() {
                    for i in ($target_type::MIN..$max as $target_type).step_by($step) {
                        let mut s = i.to_string();
                        s.insert(0, '+');
                        let p: Result<$target_type, ()> = s.parse().map_err(|_| ());
                        assert_eq!(p, [<parse_ $target_type $postfix>](&s).map_err(|_| ()), "fail to parse: '{}'", &s);
                    }
                }
            }
        }
    }

    gen_tests!(u8, u8::MAX, 1, 3,"", "1");
    gen_tests!(u8, u8::MAX, 1, 3,"_challenger", "1");
    
    gen_tests!(i8, i8::MAX, 1, 3,"", "1");
    gen_tests!(i8, i8::MAX, 1, 3,"_challenger", "1");
    
    gen_tests!(u16, u16::MAX, 1, 5, "","1");
    gen_tests!(u16, u16::MAX, 1, 5, "_challenger","1");

    
    gen_tests!(i16, i64::MAX, 1, 5,"", "1");
    gen_tests!(i16, i64::MAX, 1, 5,"_challenger", "1");
    
    gen_tests!(u32, u32::MAX, 10_301, 10,"", "1");
    gen_tests!(u32, u32::MAX, 10_301, 10,"_challenger", "1");

    gen_tests!(u64, u64::MAX, 100_301_000_000_000, 20, "","1");
    gen_tests!(u64, u64::MAX, 100_301_000_000_000, 20, "_challenger","1");

    gen_tests!(u128, u64::MAX, 100_301_000_000_000, 39,"", "+0");
    gen_tests!(u128, u64::MAX, 100_301_000_000_000, 39,"_challenger", "123456789012345678901234567890123456789");
}
