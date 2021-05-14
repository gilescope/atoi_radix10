use super::{parse_2_chars, parse_4_chars, parse_8_chars, ParseIntError2, MINUS, PLUS};
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

/// Parses from -2_147_483_648 to 2_147_483_647 (10 digits and optionally +/-)
pub fn parse_i32(s: &[u8]) -> Result<i32, PIE> {
    let mut s = s; //.as_bytes();
    let val = match s.get(0) {
        Some(val) => {
            let val = val.wrapping_sub(b'0');
            if val <= 9 {
                val
            } else {
                if val == MINUS {
                    s = &s[1..];
                    let val = match s.get(0) {
                        Some(val) => {
                            let val = val.wrapping_sub(b'0');
                            if val <= 9 {
                                val
                            } else {
                                return Err(PIE { kind: InvalidDigit });
                            }
                        }
                        None => return Err(PIE { kind: Empty }),
                    };
                    let l = s.len();
                    unsafe {
                        return match l {
                            1 => Ok(-(val as i32)),
                            2 => {
                                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                                if val2 <= 9 {
                                    Ok(-((val * 10 + val2) as i32))
                                } else {
                                    Err(PIE { kind: InvalidDigit })
                                }
                            }
                            3 => {
                                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                                if (val2 <= 9) & (val3 <= 9) {
                                    Ok(-(val as i32 * 100 + (val2 * 10 + val3) as i32))
                                } else {
                                    Err(PIE { kind: InvalidDigit })
                                }
                            }
                            4 => Ok(-(parse_4_chars(s)? as i32)),
                            5 => Ok(-(val as i32 * 1_0000 + parse_4_chars(&s[1..])? as i32)),
                            6 => {
                                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                                if val2 <= 9 {
                                    let result = parse_4_chars(&s[2..])? as i32;
                                    Ok(-(val as i32 * 10_0000 + val2 as i32 * 1_0000 + result))
                                } else {
                                    Err(PIE { kind: InvalidDigit })
                                }
                            }
                            7 => {
                                let val2 = parse_4_chars(&s[1..])? as i32 * 100;
                                let val3 = parse_2_chars(&s[5..])? as i32;
                                Ok(-(val as i32 * 1_000_000 + val2 + val3))
                            }
                            8 => parse_8_chars(&s).map(|val| -(val as i32)),
                            9 => {
                                let result = parse_8_chars(&s[1..])? as i32;
                                Ok(-(result + (val as i32 * 100_000_000)))
                            }
                            10 => {
                                let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as i32;
                                if (val <= 2) & (val2 <= 9) {
                                    let mut result = parse_8_chars(&s[2..])? as i32;
                                    let val = val as i32 * 1_000_000_000;
                                    val2 *= 100_000_000;
                                    result += val2;
                                    if result != 147483648 {
                                        match result.checked_add(val) {
                                            Some(val) => Ok(-(val)),
                                            None => Err(PIE { kind: NegOverflow }),
                                        }
                                    } else {
                                        return Ok(i32::MIN);
                                    }
                                } else {
                                    return Err(PIE { kind: NegOverflow });
                                }
                            }
                            _ => Err(PIE { kind: InvalidDigit }),
                        };
                    }
                }
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
            1 => Ok(val as i32),
            2 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    Ok((val * 10 + val2) as i32)
                } else {
                    Err(PIE { kind: InvalidDigit })
                }
            }
            3 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                let val3 = s.get_unchecked(2).wrapping_sub(b'0');
                if (val2 <= 9) & (val3 <= 9) {
                    Ok(val as i32 * 100 + (val2 * 10 + val3) as i32)
                } else {
                    Err(PIE { kind: InvalidDigit })
                }
            }
            4 => Ok(parse_4_chars(s)? as i32),
            5 => Ok(val as i32 * 1_0000 + parse_4_chars(&s[1..])? as i32),
            6 => {
                let val2 = s.get_unchecked(1).wrapping_sub(b'0');
                if val2 <= 9 {
                    let result = parse_4_chars(&s[2..])? as i32;
                    Ok(val as i32 * 10_0000 + val2 as i32 * 1_0000 + result)
                } else {
                    Err(PIE { kind: InvalidDigit })
                }
            }
            7 => {
                let val2 = parse_4_chars(&s[1..])? as i32 * 100;
                let val3 = parse_2_chars(&s[5..])? as i32;
                Ok(val as i32 * 1_000_000 + val2 + val3)
            }
            8 => parse_8_chars(&s).map(|val| val as i32),
            9 => {
                let result = parse_8_chars(&s[1..])? as i32;
                Ok(result + (val as i32 * 100_000_000))
            }
            10 => {
                let mut val2 = s.get_unchecked(1).wrapping_sub(b'0') as i32;
                if (val <= 2) & (val2 <= 9) {
                    let mut result = parse_8_chars(&s[2..])? as i32;
                    let val = val as i32 * 1_000_000_000;
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
                    if l - pos <= 11 {
                        if s[pos] != b'+' {
                            return parse_i32(&s[pos..]);
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

pub fn parse_i32_challenger(s: &[u8]) -> Result<i32, PIE> {
    parse_i32(s)
}
