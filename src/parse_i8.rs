use super::{ParseIntError2, PLUS};
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

pub fn parse_i8(s: &[u8]) -> Result<i8, PIE> {
    let mut iter = s.iter();
    match iter.next() {
        Some(val) => {
            if *val == b'-' {
                return match iter.next() {
                    Some(val) => {
                        let mut val = val.wrapping_sub(b'0');
                        if val <= 9 {
                            while val == 0 {
                                val = match iter.next() {
                                    Some(val2) => val2.wrapping_sub(b'0'),
                                    None => {
                                        return Ok(0);
                                    }
                                }
                            }
                            match iter.next() {
                                None => Ok(-(val as i8)),
                                Some(val2) => {
                                    let val2 = val2.wrapping_sub(b'0');
                                    if val2 <= 9 {
                                        match iter.next() {
                                            None => Ok(-((val * 10 + val2) as i8)),
                                            Some(val3) => match iter.next() {
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
                                                }
                                                Some(_) => return Err(PIE { kind: PosOverflow }),
                                            },
                                        }
                                    } else {
                                        Err(PIE { kind: InvalidDigit })
                                    }
                                }
                            }
                        } else {
                            Err(PIE { kind: InvalidDigit })
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
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            while val == 0 {
                val = match iter.next() {
                    Some(val2) => val2.wrapping_sub(b'0'),
                    None => {
                        return Ok(0);
                    }
                }
            }
            match iter.next() {
                None => Ok(val as i8),
                Some(val2) => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 <= 9 {
                        match iter.next() {
                            None => Ok((val * 10 + val2) as i8),
                            Some(val3) => match iter.next() {
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
                            },
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

pub fn parse_i8_challenger(s: &[u8]) -> Result<i8, PIE> {
    parse_i8(s)
}

// pub fn parse_i8_challenger(s: &[u8]) -> Result<i8, PIE> {
//     let mut iter = s.iter();
//     match iter.next() {
//         Some(mut val) => {
//             if *val == b'-' {
//                 return match iter.next() {
//                     Some(val) => {
//                         let val = val.wrapping_sub(b'0');
//                         if val <= 9 {
//                             match iter.next() {
//                                 None => Ok(-(val as i8)),
//                                 Some(val2) => {
//                                     let val2 = val2.wrapping_sub(b'0');
//                                     if val2 <= 9 {
//                                         match iter.next() {
//                                             None => Ok(-((val * 10 + val2) as i8)),
//                                             Some(val3) => match iter.next() {
//                                                 None => {
//                                                     let val3 = val3.wrapping_sub(b'0');
//                                                     if (val3 <= 9) & (val <= 1) {
//                                                         let result = val * 100 + val2 * 10 + val3;
//                                                         if result < 128 {
//                                                             Ok(-(result as i8))
//                                                         } else if result == 128 {
//                                                             Ok(i8::MIN)
//                                                         } else {
//                                                             Err(PIE { kind: PosOverflow })
//                                                         }
//                                                     } else {
//                                                         Err(PIE { kind: PosOverflow })
//                                                     }
//                                                 }
//                                                 Some(_) => return Err(PIE { kind: PosOverflow }),
//                                             },
//                                         }
//                                     } else {
//                                         Err(PIE { kind: InvalidDigit })
//                                     }
//                                 }
//                             }
//                         } else {
//                             Err(PIE { kind: InvalidDigit })
//                         }
//                     }
//                     _ => Err(PIE { kind: InvalidDigit }),
//                 };
//             } else if *val == b'+' {
//                 match iter.next() {
//                     Some(alt_val) => {
//                         val = alt_val;
//                     }
//                     None => return Err(PIE { kind: InvalidDigit }),
//                 }
//             }
//             let val = val.wrapping_sub(b'0');
//             match iter.next() {
//                 None => {
//                     if val <= 9 {
//                         Ok(val as i8)
//                     } else {
//                         Err(PIE { kind: InvalidDigit })
//                     }
//                 }
//                 Some(val2) => {
//                     let val2 = val2.wrapping_sub(b'0');
//                     if val2 <= 9 {
//                         match iter.next() {
//                             None => {
//                                 if val <= 9 {
//                                     Ok((val * 10 + val2) as i8)
//                                 } else {
//                                     Err(PIE { kind: InvalidDigit })
//                                 }
//                             }
//                             Some(val3) => match iter.next() {
//                                 None => {
//                                     let val3 = val3.wrapping_sub(b'0');
//                                     let val2 = val2 * 10;
//                                     if (val3 <= 9) & (val <= 1) {
//                                         let result = val * 100 + val2 + val3;
//                                         if result < 128 {
//                                             Ok(result as i8)
//                                         } else {
//                                             Err(PIE { kind: PosOverflow })
//                                         }
//                                     } else {
//                                         return Err(PIE { kind: PosOverflow });
//                                     }
//                                 }
//                                 Some(_) => return Err(PIE { kind: PosOverflow }),
//                             },
//                         }
//                     } else {
//                         return Err(PIE { kind: InvalidDigit });
//                     }
//                 }
//             }
//         }
//         _ => Err(PIE { kind: Empty }),
//     }
// }

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
