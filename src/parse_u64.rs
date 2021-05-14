use super::{
    parse_16_chars, parse_2_chars, parse_4_chars, parse_8_chars, trees::TENS_U64, ParseIntError2,
};
use core::num::IntErrorKind::*;

type PIE = ParseIntError2;

// Parses 0 to 18_446_744_073_709_551_615 (up to 20 chars)
// pub fn parse_u64(s: &[u8]) -> Result<u64, PIE> {
//     unsafe {
//         let mut s = s; //.as_bytes();
//         let (val, val2) = match s.get(0) {
//             Some(val) => {
//                 let val = if *val == b'+' {
//                     s = &s.get_unchecked(1..);
//                     match s.get(0) {
//                         Some(val) => val,
//                         None => return Err(PIE { kind: InvalidDigit }),
//                     }
//                 } else {
//                     val
//                 };

//                 let val2 = match s.get(1) {
//                     Some(val2) => val2,
//                     None => {
//                         let val = val.wrapping_sub(b'0');
//                         return if val <= 9 {
//                             Ok(val as u64)
//                         } else {
//                             Err(PIE { kind: InvalidDigit })
//                         };
//                     }
//                 };

//                 (val, val2)
//             }
//             None => return Err(PIE { kind: Empty }),
//         };

//         let l = s.len();
//         let mut res = 0;
//         if l & 2 != 0 {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             if (val > 9) | (val2 > 9) {
//                 return Err(PIE { kind: InvalidDigit });
//             };
//             res += val as u64 * TENS_U64.get_unchecked(s.len() - 1)
//                 + val2 as u64 * TENS_U64.get_unchecked(s.len() - 2);
//             s = &s.get_unchecked(2..);
//         }
//         if l & 1 != 0 {
//             let val = s.get_unchecked(0).wrapping_sub(b'0');
//             if val > 9 {
//                 return Err(PIE { kind: InvalidDigit });
//             };
//             s = &s.get_unchecked(1..);
//             res += val as u64 * TENS_U64.get_unchecked(s.len());
//         }
//         if l & 16 != 0 {
//             let val16 = parse_16_chars(&s)?;
//             if l >= 20 {
//                 // Treat checked case separately
//                 if l == 20 {
//                     //TODO what if l & 32 but not 16?
//                     let val = match val16.checked_mul(10_000) {
//                         Some(val) => val,
//                         None => return Err(PIE { kind: PosOverflow }),
//                     };
//                     return match val.checked_add(parse_4_chars(&s[16..])? as u64) {
//                         Some(val) => Ok(val),
//                         None => Err(PIE { kind: PosOverflow }),
//                     };
//                 }
//                 let pos = s.iter().position(|byte| *byte != b'0');
//                 if let Some(pos) = pos {
//                     if l - pos <= 20 {
//                         if s[pos] != b'+' {
//                             return parse_u64(&s[pos..]);
//                         } else {
//                             return Err(PIE { kind: InvalidDigit });
//                         }
//                     }
//                 } else {
//                     return Ok(0);
//                 }
//                 return Err(PIE { kind: PosOverflow });
//             }
//             s = &s.get_unchecked(16..);
//             res += val16 * TENS_U64.get_unchecked(s.len()); //TODO always 1
//         }
//         if l & 8 != 0 {
//             let val = parse_8_chars(&s)? as u64;
//             s = &s.get_unchecked(8..);
//             res += val * TENS_U64.get_unchecked(s.len());
//         }
//         if l & 4 != 0 {
//             res += parse_4_chars(&s)? as u64;
//         }
//         Ok(res)
//     }
// }
pub fn parse_u64(ss: &[u8]) -> Result<u64, PIE> {
    super::parse::<u64>(ss).map_err(|_| PIE { kind: InvalidDigit })
}
pub fn parse_u64_challenger(ss: &[u8]) -> Result<u64, PIE> {
    super::parse::<u64>(ss).map_err(|_| PIE { kind: InvalidDigit })
}
// Parses 0 to 18_446_744_073_709_551_615 (up to 20 chars)
// pub fn parse_u64_challenger(ss: &[u8]) -> Result<u64, PIE> {
//     let mut s = ss; //.as_bytes();
//     let (val, val2) = match s.get(0) {
//         Some(val) => {
//             let val = if *val == b'+' {
//                 s = &s[1..];
//                 match s.get(0) {
//                     Some(val) => val,
//                     None => return Err(PIE { kind: InvalidDigit }),
//                 }
//             } else {
//                 val
//             };

//             let val2 = match s.get(1) {
//                 Some(val2) => val2,
//                 None => {
//                     let val = val.wrapping_sub(b'0');
//                     return if val <= 9 {
//                         Ok(val as u64)
//                     } else {
//                         Err(PIE { kind: InvalidDigit })
//                     };
//                 }
//             };

//             (val, val2)
//         }
//         None => return Err(PIE { kind: Empty }),
//     };
//     let l = s.len();
//     match l {
//         2 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             if (val <= 9) & (val2 <= 9) {
//                 return Ok((val * 10 + val2) as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             };
//         }
//         3 => {
//             let val = val.wrapping_sub(b'0');
//             let val2 = val2.wrapping_sub(b'0');
//             let val3 = s[2].wrapping_sub(b'0');
//             if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
//                 return Ok((val as u16 * 100 + (val2 as u16 * 10 + val3 as u16)) as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             };
//         }
//         4 => Ok(parse_4_chars(s)? as u64),
//         5 => {
//             let result = parse_4_chars(&s[1..])? as u32;
//             let val = val.wrapping_sub(b'0');
//             if val <= 9 {
//                 return Ok((result + (val as u32 * 10_000)) as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         6 => {
//             let result = parse_4_chars(s)? as u32;
//             let val = parse_2_chars(&s[4..])?;
//             Ok((result * 100 + val as u32) as u64)
//         }
//         7 => {
//             let result = parse_4_chars(&s[1..])? as u32;
//             let loose_change = parse_2_chars(&s[5..])? as u32;
//             let val = val.wrapping_sub(b'0') as u32;
//             if val <= 9 {
//                 return Ok((val * 1_000_000 + result * 100 + loose_change) as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         8 => parse_8_chars(&s).map(|val| val as u64),
//         9 => {
//             let val = val.wrapping_sub(b'0') as u32;
//             let result = parse_8_chars(&s[1..])?;
//             if val <= 9 {
//                 return Ok((result + (val as u32 * 100_000_000)) as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         10 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) {
//                 let result = parse_8_chars(&s[2..])? as u64;
//                 return Ok(val * 1_000_000_000 + val2 * 100_000_000 + result);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         11 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             let val3 = s[2].wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
//                 let result = parse_8_chars(&s[3..])? as u64;
//                 return Ok(val * 10_000_000_000
//                     + val2 * 1_000_000_000
//                     + val3 * 100_000_000
//                     + result);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         12 => return Ok(parse_4_chars(s)? as u64 * 1_0000_0000 + parse_8_chars(&s[4..])? as u64),
//         13 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             if val <= 9 {
//                 return Ok(val as u64 * 1_0000_0000_0000
//                     + parse_4_chars(&s[1..])? as u64 * 1_0000_0000
//                     + parse_8_chars(&s[5..])? as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         14 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) {
//                 return Ok(val as u64 * 10_0000_0000_0000
//                     + val2 as u64 * 1_0000_0000_0000
//                     + parse_4_chars(&s[2..])? as u64 * 1_0000_0000
//                     + parse_8_chars(&s[6..])? as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         15 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             let val3 = s[2].wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
//                 return Ok(val as u64 * 100_0000_0000_0000
//                     + val2 as u64 * 10_0000_0000_0000
//                     + val3 as u64 * 1_0000_0000_0000
//                     + parse_4_chars(&s[3..])? as u64 * 1_0000_0000
//                     + parse_8_chars(&s[7..])? as u64);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         16 => parse_16_chars(s),
//         17 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             if val <= 9 {
//                 return Ok(val * 10_000_000_000_000_000 + parse_16_chars(&s[1..])?);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         18 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) {
//                 return Ok(val * 100_000_000_000_000_000
//                     + val2 * 10_000_000_000_000_000
//                     + parse_16_chars(&s[2..])?);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         19 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             let val2 = val2.wrapping_sub(b'0') as u64;
//             let val3 = s[2].wrapping_sub(b'0') as u64;
//             if (val <= 9) & (val2 <= 9) & (val3 <= 9) {
//                 return Ok(val * 1_000_000_000_000_000_000
//                     + val2 * 100_000_000_000_000_000
//                     + val3 * 10_000_000_000_000_000
//                     + parse_16_chars(&s[3..])?);
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         20 => {
//             let val = val.wrapping_sub(b'0') as u64;
//             if val <= 1 {
//                 match (parse_4_chars(&s)? as u64 * 10_000_000_000_000_000)
//                     .checked_add(parse_16_chars(&s[4..])? as u64)
//                 {
//                     Some(val) => return Ok(val),
//                     None => return Err(PIE { kind: PosOverflow }),
//                 }
//             }
//             return Err(PIE { kind: PosOverflow });
//         }
//         _ => {
//             let pos = s.iter().position(|byte| *byte != b'0');
//             if let Some(pos) = pos {
//                 if l - pos <= 20 {
//                     if s[pos] != b'+' {
//                         return parse_u64(&s[pos..]);
//                     } else {
//                         return Err(PIE { kind: InvalidDigit });
//                     }
//                 }
//             } else {
//                 return Ok(0);
//             }
//             return Err(PIE { kind: PosOverflow });
//         }
//     }
// }

// Parses 0 to 18_446_744_073_709_551_615
// pub fn parse_u64_old_best(ss: &str) -> Result<u64, ()> {
//     let mut l = ss.len();
//     if l < 10 {
//         return parse_u32(ss).map(|val| val as u64);
//     }
//     let mut s = ss.as_bytes();

//     match s.get(0) {
//         None => return Err(()),
//         Some(val) if *val == b'+' => {
//             s = &s[1..];
//             l -= 1;
//         }
//         Some(_) => {}
//     }

//     if l > 20 {
//         return Err(());
//     }

//     let mut result: u64 = 0;
//     while l >= 8 {
//         result = 100_000_000 * result + parse_8_chars(&s[..8])? as u64;
//         s = &s[8..];
//         l -= 8;
//     }
//     if l >= 4 {
//         // 20 chars comes here so we need to checked math.
//         result = match result.checked_mul(10_000) {
//             Some(val) => val,
//             None => return Err(()),
//         };
//         result = match result.checked_add(parse_4_chars(&s[..4])? as u64) {
//             Some(val) => val,
//             None => return Err(()),
//         };
//         s = &s[4..];
//         l -= 4;
//     }
//     if l >= 2 {
//         result = result * 100 + parse_2_chars(&s[..2])? as u64;
//         s = &s[2..];
//         l -= 2;
//     }
//     if l == 1 {
//         let val = s[0].wrapping_sub(b'0');
//         if val > 9 {
//             return Err(());
//         }
//         result = result * 10 + val as u64;
//     }
//     return Ok(result);
// }
