use super::{
    parse_16_chars, parse_4_chars, parse_8_chars, ParseIntError2, TENS_U128,
};
use std::num::IntErrorKind::*;

type PIE = ParseIntError2;

pub fn parse_i128_challenger(s: &str) -> Result<i128, PIE> {
    parse_i128(s)
}

/// i128: -170141183460469231731687303715884105728 to 170141183460469231731687303715884105727, 
/// (39 digits!)
pub fn parse_i128(s: &str) -> Result<i128, PIE> {
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
                                        Ok(-(val as i128))
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
                    return if l < 39 {
                        let mut res = 0i128;
                        if l & 2 != 0 {
                            let val = val.wrapping_sub(b'0');
                            let val2 = val2.wrapping_sub(b'0');
                            if (val <= 9) & (val2 <= 9) {
                                res += val as i128 * *TENS_U128.get_unchecked(s.len() - 1) as i128
                                    + val2 as i128 * *TENS_U128.get_unchecked(s.len() - 2) as i128;
                                s = &s.get_unchecked(2..);
                            } else {
                                return Err(PIE { kind: InvalidDigit });
                            };
                        }
                        if l & 1 != 0 {
                            let val = s.get_unchecked(0).wrapping_sub(b'0');
                            if val <= 9 {
                                s = &s.get_unchecked(1..);
                                res += val as i128 * *TENS_U128.get_unchecked(s.len()) as i128;
                            } else {
                                return Err(PIE { kind: InvalidDigit });
                            };
                        }
                        if l & 16 != 0 {
                            let val16 = parse_16_chars(&s)? as i128;
                            s = &s.get_unchecked(16..);
                            res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;
                        }
                        if l & 8 != 0 {
                            let val = parse_8_chars(&s)? as i128;
                            s = &s.get_unchecked(8..);
                            res += val * *TENS_U128.get_unchecked(s.len()) as i128;
                        }
                        if l & 32 != 0 {
                            let val16 = parse_16_chars(&s)? as i128;
                            s = &s.get_unchecked(16..);
                            res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;

                            // Do the same thing again as a parse_32_chars fn would need 256bits.
                            let val16 = parse_16_chars(&s)? as i128;
                            s = &s.get_unchecked(16..);
                            res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;
                        }
                        if l & 4 != 0 {
                            res += parse_4_chars(&s)? as i128;
                        }
                        Ok(-res)
                    } else {
                        if l == 39 {
                            //39 = 32 + 4 + 2 + 1
                            let val = val.wrapping_sub(b'0');
                            if val > 1 {
                                return Err(PIE { kind: PosOverflow });
                            }
                            let val = val as i128 * TENS_U128[38] as i128;

                            let val2 = val2.wrapping_sub(b'0');
                            let val3 = s[2].wrapping_sub(b'0');
                            if (val2 <= 9) & (val3 <= 9) {
                                let mut res = val2 as i128 * *TENS_U128.get_unchecked(37) as i128
                                    + val3 as i128 * *TENS_U128.get_unchecked(36) as i128;
                                s = &s.get_unchecked(3..);

                                let val16 = parse_16_chars(&s)? as i128;
                                s = &s.get_unchecked(16..);
                                res += val16 * *TENS_U128.get_unchecked(20) as i128;

                                // Do the same thing again as a parse_32_chars fn would need 256bits.
                                let val16 = parse_16_chars(&s)? as i128;
                                s = &s.get_unchecked(16..);
                                res += val16 * *TENS_U128.get_unchecked(4) as i128;
                                res += parse_4_chars(&s)? as i128;

                                match val.checked_add(res) {
                                    Some(val) => Ok(-val),
                                    None => {
                                        if val == 100000000000000000000000000000000000000 && res == 70141183460469231731687303715884105728 {
                                            Ok(i128::MIN)
                                        } else {
                                            Err(PIE { kind: NegOverflow })
                                        }
                                    },
                                }
                            } else {
                                Err(PIE { kind: InvalidDigit })
                            }
                        } else {
                            Err(PIE { kind: NegOverflow })
                        }
                    }
                } else if *val == b'+' {
                    s = &s.get_unchecked(1..);
                    match s.get(0) {
                        Some(val) => val,
                        None => return Err(PIE { kind: Empty }),
                    }
                } else {
                    val
                };

                let val2 = match s.get(1) {
                    Some(val2) => val2,
                    None => {
                        let val = val.wrapping_sub(b'0');
                        return if val <= 9 {
                            Ok(val as i128)
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
        if l < 39 {
            let mut res = 0i128;
            if l & 2 != 0 {
                let val = val.wrapping_sub(b'0');
                let val2 = val2.wrapping_sub(b'0');
                if (val <= 9) & (val2 <= 9) {
                    res += val as i128 * *TENS_U128.get_unchecked(s.len() - 1) as i128
                        + val2 as i128 * *TENS_U128.get_unchecked(s.len() - 2) as i128;
                    s = &s.get_unchecked(2..);
                } else {
                    return Err(PIE { kind: InvalidDigit });
                };
            }
            if l & 1 != 0 {
                let val = s.get_unchecked(0).wrapping_sub(b'0');
                if val <= 9 {
                    s = &s.get_unchecked(1..);
                    res += val as i128 * *TENS_U128.get_unchecked(s.len()) as i128;
                } else {
                    return Err(PIE { kind: InvalidDigit });
                };
            }
            if l & 16 != 0 {
                let val16 = parse_16_chars(&s)? as i128;
                s = &s.get_unchecked(16..);
                res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;
            }
            if l & 8 != 0 {
                let val = parse_8_chars(&s)? as i128;
                s = &s.get_unchecked(8..);
                res += val * *TENS_U128.get_unchecked(s.len()) as i128;
            }
            if l & 32 != 0 {
                let val16 = parse_16_chars(&s)? as i128;
                s = &s.get_unchecked(16..);
                res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;

                // Do the same thing again as a parse_32_chars fn would need 256bits.
                let val16 = parse_16_chars(&s)? as i128;
                s = &s.get_unchecked(16..);
                res += val16 * *TENS_U128.get_unchecked(s.len()) as i128;
            }
            if l & 4 != 0 {
                res += parse_4_chars(&s)? as i128;
            }

            Ok(res)
        } else {
            if l == 39 {
                //39 = 32 + 4 + 2 + 1
                let val = val.wrapping_sub(b'0');
                if val > 1 {
                    return Err(PIE { kind: PosOverflow });
                }
                let val = val as i128 * TENS_U128[38] as i128;

                let val2 = val2.wrapping_sub(b'0');
                let val3 = s[2].wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    let mut res = val2 as i128 * *TENS_U128.get_unchecked(37) as i128
                        + val3 as i128 * *TENS_U128.get_unchecked(36) as i128;
                    s = &s.get_unchecked(3..);

                    let val16 = parse_16_chars(&s)? as i128;
                    s = &s.get_unchecked(16..);
                    res += val16 * *TENS_U128.get_unchecked(20) as i128;

                    // Do the same thing again as a parse_32_chars fn would need 256bits.
                    let val16 = parse_16_chars(&s)? as i128;
                    s = &s.get_unchecked(16..);
                    res += val16 * *TENS_U128.get_unchecked(4) as i128;

                    res += parse_4_chars(&s)? as i128;

                    match val.checked_add(res) {
                        Some(val) => Ok(val),
                        None => Err(PIE { kind: PosOverflow }),
                    }
                } else {
                    Err(PIE { kind: InvalidDigit })
                }
            } else {
                Err(PIE { kind: PosOverflow })
            }
        }
    }
}
