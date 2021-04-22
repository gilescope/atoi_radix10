use super::{ParseIntError2, PLUS};
use std::num::IntErrorKind::*;

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
