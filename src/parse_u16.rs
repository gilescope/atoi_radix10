use super::{parse_2_chars, parse_4_chars, ParseIntError2, PLUS};
use std::num::IntErrorKind::*;

type PIE = ParseIntError2;


pub fn parse_u16(s: &str) -> Result<u16, PIE> {
    let mut s = s.as_bytes();
    let mut l: usize;
    let val = match s.get(0) {
        Some(&val) => {
            l = s.len();
            if l == 1 {
                let val = val.wrapping_sub(b'0');
                let v = val as u16;
                return if val <= 9 {
                    Ok(v)
                } else {
                    Err(PIE { kind: InvalidDigit })
                };
            } else if val == b'+' {
                s = &s[1..];
                l -= 1;
                match s.get(0) {
                    Some(&val) => {
                        if l == 1 {
                            let val = val.wrapping_sub(b'0');
                            return if val <= 9 {
                                Ok(val as u16)
                            } else {
                                Err(PIE { kind: InvalidDigit })
                            };
                        }
                        val
                    },
                    None => return Err(PIE { kind: InvalidDigit }),
                }
            } else { val }
        }
        None => return Err(PIE { kind: Empty }),
    };

    match l {
        2 => parse_2_chars(s),
        3 => {
            let val = val.wrapping_sub(b'0');
            let val1 = val as u16 * 100;
            if val <= 9 {
                return Ok(val1 + parse_2_chars(&s[1..])?);
            } else {return Err(PIE { kind: InvalidDigit })};
        }
        4 => parse_4_chars(s),
        5 => {
            let val = val.wrapping_sub(b'0');
            let val1 = val as u16 * 10_000;
            let res = parse_4_chars(&s[1..])?;
            if val <= 6 {
                match val1.checked_add(res) {
                    Some(val) => Ok(val),
                    None => return Err(PIE { kind: PosOverflow }),
                }
            } else {
                Err(PIE { kind: PosOverflow })
            }
        }
        _ => Err(PIE { kind: PosOverflow }),
    }
}

pub fn parse_u16_challenger(s: &str) -> Result<u16, PIE> {
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
                    return Ok(val as u16);
                }
                Some(val2) => val2,
            };
            let val3 = match s.get(2) {
                None => {
                    let val2 = val2.wrapping_sub(b'0');
                    if val2 > 9 {
                        return Err(PIE { kind: InvalidDigit });
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
                return Err(PIE { kind: InvalidDigit });
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
