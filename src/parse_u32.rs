use super::{parse_2_chars, parse_4_chars, parse_8_chars, ParseIntError2, PLUS};
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

/// Parses from 0 -> 4_294_967_295 (10 digits and optionally +)
pub fn parse_u32(mut s: &[u8]) -> Result<u32, PIE> {
   // let mut s = s.as_bytes();
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
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
        }
        None => return Err(PIE { kind: Empty }),
    };
    let mut l = s.len();
    unsafe {
        match l {
            1 => Ok(val as u32),
            2 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    Ok((val * 10 + val2) as u32)
                } else {
                    Err(PIE { kind: InvalidDigit })
                }
            }
            3 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
                } else {
                    Err(PIE { kind: InvalidDigit })
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
                    Err(PIE { kind: InvalidDigit })
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
            _ => {
                let pos = s.iter().position(|byte| *byte != b'0');
                if let Some(pos) = pos {
                    if l - pos <= 10 {
                        if s[pos] != b'+' {
                            return parse_u32(&s[pos..])
                        } else {
                            return Err(PIE { kind: InvalidDigit });
                        }
                    }
                } else {
                    return Ok(0);
                }
                return Err(PIE { kind: PosOverflow });
            },
        }
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
pub fn parse_u32_challenger(s: &[u8]) -> Result<u32, PIE> {
    //TODO: can we accept AsRef<[u8]> or IntoRef<u8]> ?
    let mut s = s;//.as_bytes();
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
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
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
                    Err(PIE { kind: InvalidDigit })
                }
            }
            3 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    Ok(val as u32 * 100 + (val2 * 10 + val3) as u32)
                } else {
                    Err(PIE { kind: InvalidDigit })
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
                    Err(PIE { kind: InvalidDigit })
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
                    Err(PIE { kind: InvalidDigit })
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
