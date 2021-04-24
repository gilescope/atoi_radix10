use super::{parse_16_chars, parse_4_chars, parse_8_chars, ParseIntError2, TENS_U64};
use std::num::IntErrorKind::*;

type PIE = ParseIntError2;

/// Parses -9_223_372_036_854_775_808 -> 9_223_372_036_854_775_807 (up to 19 chars)
pub fn parse_i64(s: &str) -> Result<i64, PIE> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'-' {
                    s = &s.get_unchecked(1..);
                    let (val, val2) = match s.get(0) {
                        Some(val) => {
                            let val2 = match s.get(1) {
                                Some(val2) => val2,
                                None => {
                                    let val = val.wrapping_sub(b'0');
                                    return if val <= 9 {
                                        Ok(-(val as i64))
                                    } else {
                                        Err(PIE { kind: InvalidDigit })
                                    };
                                }
                            };
                            (val, val2)
                        }
                        None => return Err(PIE { kind: Empty }),
                    };

                    let l = s.len();
                    let mut res = 0i64;
                    if l & 2 != 0 {
                        let val = val.wrapping_sub(b'0');
                        let val2 = val2.wrapping_sub(b'0');
                        if (val > 9) | (val2 > 9) {
                            return Err(PIE { kind: InvalidDigit });
                        };
                        let ln = s.len();
                        res += val as i64 * *TENS_U64.get_unchecked(ln - 1) as i64
                            + val2 as i64 * *TENS_U64.get_unchecked(ln - 2) as i64;
                        s = &s.get_unchecked(2..);
                    }
                    if l & 1 != 0 {
                        let val = s.get_unchecked(0).wrapping_sub(b'0');
                        if val > 9 {
                            return Err(PIE { kind: InvalidDigit });
                        };
                        s = &s.get_unchecked(1..);
                        res += val as i64 * *TENS_U64.get_unchecked(s.len()) as i64;
                    }
                    if l & 16 != 0 {
                        let val16 = parse_16_chars(&s)? as i64;
                        if l >= 19 {
                            // Treat checked case separately
                            if l == 19 {
                                //TODO what if l & 32 but not 16?
                                return match val16.checked_add(res) {
                                    Some(val) => Ok(-val),
                                    None => {
                                        if val16 == 3_372_036_854_775_808
                                            && res == 9220_000_000_000_000_000
                                        {
                                            return Ok(i64::MIN);
                                        }
                                        Err(PIE { kind: PosOverflow })
                                    }
                                };
                            }
                            return Err(PIE { kind: PosOverflow });
                        }
                        s = &s.get_unchecked(16..);
                        res += val16 * *TENS_U64.get_unchecked(s.len()) as i64; //TODO always 1
                    }
                    if l & 8 != 0 {
                        let val = parse_8_chars(&s)? as i64;
                        s = &s.get_unchecked(8..);
                        res += val * *TENS_U64.get_unchecked(s.len()) as i64;
                    }
                    if l & 4 != 0 {
                        res += parse_4_chars(&s)? as i64;
                    }
                    return Ok(-res);
                } else if *val == b'+' {
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
                            Ok(val as i64)
                        } else {
                            Err(PIE { kind: InvalidDigit })
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
                return Err(PIE { kind: InvalidDigit });
            };
            res += val as i64 * *TENS_U64.get_unchecked(s.len() - 1) as i64
                + val2 as i64 * *TENS_U64.get_unchecked(s.len() - 2) as i64;
            s = &s.get_unchecked(2..);
        }
        if l & 1 != 0 {
            let val = s.get_unchecked(0).wrapping_sub(b'0');
            if val > 9 {
                return Err(PIE { kind: InvalidDigit });
            };
            s = &s.get_unchecked(1..);
            res += val as i64 * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 16 != 0 {
            let val16 = parse_16_chars(&s)? as i64;
            if l >= 19 {
                // Treat checked case separately
                if l == 19 {
                    //TODO what if l & 32 but not 16?
                    // let val = match val16.checked_mul(10_00) {
                    //     Some(val) => val,
                    //     None => return Err(PIE { kind: PosOverflow }),
                    // };
                    return match val16.checked_add(res) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    };
                }
                return Err(PIE { kind: PosOverflow });
            }
            s = &s.get_unchecked(16..);
            res += val16 * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 8 != 0 {
            let val = parse_8_chars(&s)? as i64;
            s = &s.get_unchecked(8..);
            res += val * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 4 != 0 {
            res += parse_4_chars(&s)? as i64;
        }
        Ok(res)
    }
}

/// Parses -9_223_372_036_854_775_808 -> 9_223_372_036_854_775_807 (up to 19 chars)
pub fn parse_i64_challenger(s: &str) -> Result<i64, PIE> {
    unsafe {
        let mut s = s.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'-' {
                    s = &s.get_unchecked(1..);
                    let (val, val2) = match s.get(0) {
                        Some(val) => {
                            let val2 = match s.get(1) {
                                Some(val2) => val2,
                                None => {
                                    let val = val.wrapping_sub(b'0');
                                    return if val <= 9 {
                                        Ok(-(val as i64))
                                    } else {
                                        Err(PIE { kind: InvalidDigit })
                                    };
                                }
                            };
                            (val, val2)
                        }
                        None => return Err(PIE { kind: Empty }),
                    };

                    let l = s.len();
                    let mut res = 0i64;
                    if l & 2 != 0 {
                        let val = val.wrapping_sub(b'0');
                        let val2 = val2.wrapping_sub(b'0');
                        if (val > 9) | (val2 > 9) {
                            return Err(PIE { kind: InvalidDigit });
                        };
                        let ln = s.len();
                        res += val as i64 * *TENS_U64.get_unchecked(ln - 1) as i64
                            + val2 as i64 * *TENS_U64.get_unchecked(ln - 2) as i64;
                        s = &s.get_unchecked(2..);
                    }
                    if l & 1 != 0 {
                        let val = s.get_unchecked(0).wrapping_sub(b'0');
                        if val > 9 {
                            return Err(PIE { kind: InvalidDigit });
                        };
                        s = &s.get_unchecked(1..);
                        res += val as i64 * *TENS_U64.get_unchecked(s.len()) as i64;
                    }
                    if l & 16 != 0 {
                        let val16 = parse_16_chars(&s)? as i64;
                        if l >= 19 {
                            // Treat checked case separately
                            if l == 19 {
                                //TODO what if l & 32 but not 16?
                                return match val16.checked_add(res) {
                                    Some(val) => Ok(-val),
                                    None => {
                                        if val16 == 3_372_036_854_775_808
                                            && res == 9220_000_000_000_000_000
                                        {
                                            return Ok(i64::MIN);
                                        }
                                        Err(PIE { kind: PosOverflow })
                                    }
                                };
                            }
                            return Err(PIE { kind: PosOverflow });
                        }
                        s = &s.get_unchecked(16..);
                        res += val16 * *TENS_U64.get_unchecked(s.len()) as i64; //TODO always 1
                    }
                    if l & 8 != 0 {
                        let val = parse_8_chars(&s)? as i64;
                        s = &s.get_unchecked(8..);
                        res += val * *TENS_U64.get_unchecked(s.len()) as i64;
                    }
                    if l & 4 != 0 {
                        res += parse_4_chars(&s)? as i64;
                    }
                    return Ok(-res);
                } else if *val == b'+' {
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
                            Ok(val as i64)
                        } else {
                            Err(PIE { kind: InvalidDigit })
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
                return Err(PIE { kind: InvalidDigit });
            };
            res += val as i64 * *TENS_U64.get_unchecked(s.len() - 1) as i64
                + val2 as i64 * *TENS_U64.get_unchecked(s.len() - 2) as i64;
            s = &s.get_unchecked(2..);
        }
        if l & 1 != 0 {
            let val = s.get_unchecked(0).wrapping_sub(b'0');
            if val > 9 {
                return Err(PIE { kind: InvalidDigit });
            };
            s = &s.get_unchecked(1..);
            res += val as i64 * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 16 != 0 {
            let val16 = parse_16_chars(&s)? as i64;
            if l >= 19 {
                // Treat checked case separately
                if l == 19 {
                    //TODO what if l & 32 but not 16?
                    // let val = match val16.checked_mul(10_00) {
                    //     Some(val) => val,
                    //     None => return Err(PIE { kind: PosOverflow }),
                    // };
                    return match val16.checked_add(res) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    };
                }
                return Err(PIE { kind: PosOverflow });
            }
            s = &s.get_unchecked(16..);
            res += val16 * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 8 != 0 {
            let val = parse_8_chars(&s)? as i64;
            s = &s.get_unchecked(8..);
            res += val * *TENS_U64.get_unchecked(s.len()) as i64;
        }
        if l & 4 != 0 {
            res += parse_4_chars(&s)? as i64;
        }
        Ok(res)
    }
}
