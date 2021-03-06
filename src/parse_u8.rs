use crate::parse_2_chars;

use super::ParseIntError2;
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

/// Parse from "0" to "+255" and "+00000000255"
pub fn parse_u8(mut s: &[u8]) -> Result<u8, ParseIntError2> {
    loop {
        match s.len() {
            1 => {
                // 0
                let val = s[0].wrapping_sub(b'0');
                if val <= 9 {
                    return Ok(val);
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            3 => {
                // +00, 100
                let val23 = parse_2_chars(unsafe { &s.get_unchecked(1..) })? as u8;
                let a = 100 + val23;
                let val = unsafe { *s.get_unchecked(0) };
                if val == b'1' {
                    return Ok(a);
                } else if val == b'2' {
                    if val23 <= 55 {
                        return Ok(200 + val23);
                    } else {
                        return Err(PIE { kind: PosOverflow });
                    }
                } else if val == b'+' || val == b'0' {
                    return Ok(val23);
                } else {
                    return Err(PIE { kind: PosOverflow });
                }
            }
            2 => {
                // +0, 10
                match parse_2_chars(s) {
                    Ok(val) => return Ok(val as u8),
                    Err(_) => {
                        if s[0] == b'+' {
                            let val = s[1].wrapping_sub(b'0');
                            if val <= 9 {
                                return Ok(val);
                            }
                        }
                        return Err(PIE { kind: InvalidDigit });
                    }
                }
            }
            _ => match s.get(0) {
                Some(val) => {
                    if *val == b'+' {
                        s = &s[1..];
                    }
                    match s.iter().position(|ch| *ch != b'0') {
                        Some(pos) => {
                            s = &s[pos..];
                            if s[0] == b'+' || s.len() > 3 {
                                return Err(PIE { kind: PosOverflow });
                            }
                        }
                        None => {
                            return Ok(0);
                        }
                    }
                }
                None => {
                    return Err(PIE { kind: Empty });
                }
            },
        }
    }
}

/// Parse from "0" to "+255" and "+00000000255"
// pub fn parse_u8_challenger(s: &[u8]) -> Result<u8, ParseIntError2> {
//     let mut iter = s.iter();
//     match iter.next() {
//         Some(val) => {
//             let mut val = val.wrapping_sub(b'0');
//             if val > 9 {
//                 if val == PLUS {
//                     // '+' - '0' = 251
//                     match iter.next() {
//                         Some(alt_val) => {
//                             val = alt_val.wrapping_sub(b'0');
//                             if val > 9 {
//                                 return Err(PIE { kind: InvalidDigit });
//                             }
//                         }
//                         None => return Err(PIE { kind: InvalidDigit }),
//                     }
//                 } else {
//                     return Err(PIE { kind: InvalidDigit });
//                 }
//             }
//             while val == 0 {
//                 val = match iter.next() {
//                     Some(val2) => {
//                         val2.wrapping_sub(b'0')
//                     }
//                     None => { return Ok(0); }
//                 }
//             }
//             match iter.next() {
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 <= 9 {
//                         match iter.next() {
//                             Some(val3) => match iter.next() {
//                                 None => {
//                                     let val3 = val3.wrapping_sub(b'0');
//                                     let val2 = val2 * 10;
//                                     if val3 <= 9 {
//                                         match val {
//                                             1 => Ok(100 + val2 + val3),
//                                             2 => {
//                                                 let two = val2 + val3;
//                                                 if two <= 55 {
//                                                     Ok(200 + two)
//                                                 } else {
//                                                     Err(PIE { kind: PosOverflow })
//                                                 }
//                                             }
//                                             0 => Ok(val2 + val3),
//                                             _ => Err(PIE { kind: PosOverflow }),
//                                         }
//                                     } else {
//                                         return Err(PIE { kind: InvalidDigit });
//                                     }
//                                 }
//                                 Some(_) => return Err(PIE { kind: PosOverflow }),
//                             },
//                             None => Ok(val * 10 + val2),
//                         }
//                     } else {
//                         return Err(PIE { kind: InvalidDigit });
//                     }
//                 }
//                 None => Ok(val),
//             }
//         }
//         _ => Err(PIE { kind: Empty }),
//     }
// }

/// Parse from "0" to "+255"
pub fn parse_u8_challenger(s: &[u8]) -> Result<u8, ParseIntError2> {
    let mut iter = s.iter();
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
            let mut val = val.wrapping_sub(b'0');
            while val == 0 {
                val = match iter.next() {
                    Some(val2) => {
                        let val2 = val2.wrapping_sub(b'0');
                        if val2 > 9 {
                            return Err(PIE { kind: InvalidDigit });
                        }
                        val2
                    }
                    None => {
                        return Ok(0);
                    }
                };
            }
            match iter.next() {
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 {
                        return Err(PIE { kind: InvalidDigit });
                    }
                    match iter.next() {
                        Some(val3) => match iter.next() {
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
                            }
                            Some(_) => return Err(PIE { kind: PosOverflow }),
                        },
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
