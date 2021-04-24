use super::{parse_4_chars, ParseIntError2, MINUS, PLUS};
use std::num::IntErrorKind::*;

type PIE = ParseIntError2;

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
                                return Err(PIE { kind: InvalidDigit });
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
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        3 => {
                            let val2 = val2.wrapping_sub(b'0');
                            let val3 = s[2].wrapping_sub(b'0');
                            if (val2 <= 9) & (val3 <= 9) {
                                Ok(val as i16 * -100 + val2 as i16 * -10 - val3 as i16)
                            } else {
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        4 => parse_4_chars(s).map(|val| -(val as i16)),
                        5 => {
                            if val <= 3 {
                                let result = val as u16 * 10_000 + parse_4_chars(&s[1..])? as u16;
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
                                return Err(PIE { kind: InvalidDigit });
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
                        return Err(PIE { kind: InvalidDigit });
                    }
                }
                3 => {
                    let val2 = val2.wrapping_sub(b'0');
                    let val3 = s[2].wrapping_sub(b'0');
                    if (val2 <= 9) & (val3 <= 9) {
                        Ok(val as i16 * 100 + val2 as i16 * 10 + val3 as i16)
                    } else {
                        Err(PIE { kind: InvalidDigit })
                    }
                }
                4 => parse_4_chars(s).map(|val| val as i16),
                5 => {
                    if val <= 3 {
                        let result = val as u16 * 10_000 + parse_4_chars(&s[1..])? as u16;
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
                                } else {
                                    return Ok(-(val as i16));
                                }
                            } else {
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    };
                    unsafe {
                        return match l {
                            3 => {
                                let val2 = s.get_unchecked(2);
                                let val2 = val2.wrapping_sub(b'0');
                                if val2 <= 9 {
                                    return Ok(-((val * 10 + val2) as i16));
                                } else {
                                    return Err(PIE { kind: InvalidDigit });
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
                                    return Err(PIE { kind: InvalidDigit });
                                }
                            }
                            5 => parse_4_chars(&s.get_unchecked(1..)).map(|val| -(val as i16)),
                            6 => {
                                if val <= 3 {
                                    let result =
                                        val as u16 * 10_000 + parse_4_chars(&s.get_unchecked(2..))? as u16;
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
                                return Err(PIE { kind: InvalidDigit });
                            };
                            val
                        }
                        None => return Err(PIE { kind: InvalidDigit }),
                    }
                } else {
                    return Err(PIE { kind: InvalidDigit });
                }
            }
            if l == 1 {
                return Ok(val as i16);
            };
            match l {
                //  1 => { return Ok(val as i16); }
                2 => unsafe {
                    let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                    if val2 <= 9 {
                        return Ok((val * 10 + val2) as i16);
                    } else {
                        return Err(PIE { kind: InvalidDigit });
                    }
                },
                3 => unsafe {
                    let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                    let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                    if (val2 <= 9) & (val3 <= 9) {
                        Ok(val as i16 * 100 + val2 as i16 * 10 + val3 as i16)
                    } else {
                        Err(PIE { kind: InvalidDigit })
                    }
                },
                4 => {
                    //    Ok(0)
                    parse_4_chars(s).map(|val| val as i16)
                }
                5 => {
                    if val <= 3 {
                        let result = val as u16 * 10_000 + parse_4_chars(&s[1..])? as u16;
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
