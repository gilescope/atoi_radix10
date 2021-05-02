use super::{parse_16_chars, parse_4_chars, parse_8_chars, ParseIntError2, PLUS, TENS_U128};
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)
pub fn parse_u128_challenger(s: &[u8]) -> Result<u128, PIE> {
    unsafe {
        let mut s = s;//.as_bytes();
        let (val, val2) = match s.get(0) {
            Some(val) => {
                let val = if *val == b'+' {
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
                            Ok(val as u128)
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
            let mut res = 0u128;
            if l & 2 != 0 {
                let val = val.wrapping_sub(b'0');
                let val2 = val2.wrapping_sub(b'0');
                if (val <= 9) & (val2 <= 9) {
                    res += val as u128 * TENS_U128.get_unchecked(s.len() - 1)
                        + val2 as u128 * TENS_U128.get_unchecked(s.len() - 2);
                    s = &s.get_unchecked(2..);
                } else {
                    return Err(PIE { kind: InvalidDigit });
                };
            }
            if l & 1 != 0 {
                let val = s.get_unchecked(0).wrapping_sub(b'0');
                if val <= 9 {
                    s = &s.get_unchecked(1..);
                    res += val as u128 * TENS_U128.get_unchecked(s.len());
                } else {
                    return Err(PIE { kind: InvalidDigit });
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
                    Err(PIE { kind: InvalidDigit })
                }
            } else {
                let pos = s.iter().position(|byte| *byte != b'0');
                if let Some(pos) = pos {
                    if l - pos <= 39 {
                        if s[pos] != b'+' {
                            return parse_u128(&s[pos..])
                        } else {
                            return Err(PIE { kind: InvalidDigit });
                        }
                    }
                } else {
                    return Ok(0);
                }
                return Err(PIE { kind: PosOverflow });
            }
        }
    }
}

/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)
pub fn parse_u128(s: &[u8]) -> Result<u128, PIE> {
    unsafe {
        let mut s = s;//.as_bytes();
        let mut l: usize = s.len();

        let val = match s.get(0) {
            Some(val) => {
                let val = val.wrapping_sub(b'0');
                if val <= 9 {
                    if l == 1 {
                        return Ok(val as u128);
                    }
                    val
                } else {
                    if val == PLUS {
                        s = &s[1..];
                        let val = s[0].wrapping_sub(b'0');
                        if val <= 9 {
                            l -= 1;
                            if l == 1 {
                                return Ok(val as u128);
                            }
                            val
                        } else {
                            return Err(PIE { kind: InvalidDigit });
                        }
                    } else {
                        return Err(PIE { kind: InvalidDigit });
                    }
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
                    return Err(PIE { kind: InvalidDigit });
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
                    } else {
                        return Err(PIE { kind: InvalidDigit });
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
