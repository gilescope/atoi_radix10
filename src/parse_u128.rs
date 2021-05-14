use super::{
    parse_16_chars, parse_2_chars, parse_32_chars, parse_4_chars, parse_6_chars, parse_8_chars,
    ParseIntError2, PLUS, *,
};
use core::num::IntErrorKind::*;

type PIE = ParseIntError3;
pub fn parse_u128_challenger2(s: &[u8]) -> Result<u128, ParseIntError3> {
    //    return Ok(s[0] as u128);
    //return Err(PIE { kind: PosOverflow })
    parse::<u128>(s)
}

pub fn parse_u128_challenger(s: &[u8]) -> Result<u128, PIE> {
    // return Err(PIE { kind: IntErrorKind3::InvalidDigit })
    parse::<u128>(s)
}

pub fn parse_u128(s: &[u8]) -> Result<u128, PIE> {
    //  return Err(PIE { kind: IntErrorKind3::InvalidDigit })
    parse::<u128>(s)
}

// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
// (39 digits!)
// pub(crate) fn parse_u<T>(mut s: &[u8]) -> Result<T, PIE>
// where T: FromStrRadixHelper
//  {
//     unsafe {
//         let mut checked: Option<T> = None;
//         if let Some(val) = s.get(0) {
//             let mut val = *val;
//             loop {
//                 let l = s.len();
//                 // let val1 = val.wrapping_sub(b'0');
//                 // if l == 1 && val1 <= 9 {
//                 //     return Ok(T::from_u8(val1));
//                 // }

//                 let mut res = T::from_u8(0);
//                 if std::intrinsics::likely(val != b'+' && l < T::CHARS) {
//                     let l1 = l & 1 != 0 && T::BITS >= 4;
//                     let l2 = l & 2 != 0 && T::BITS >= 8;
//                     let l4= l & 4 != 0 && T::BITS >= 16;
//                     let l8 = l & 8 != 0 && T::BITS >= 32;
//                     let l16 = l & 16 != 0 && T::BITS >= 64;
//                     let l32 = l & 32 != 0 && T::BITS >= 128;

//                     if l1 {
//                         let val = val.wrapping_sub(b'0');
//                         let val_t = T::from_u8(val);
//                         if std::intrinsics::likely(val <= 9) {
//                             if l == 1 {
//                                 return Ok(val_t);
//                             }
//                             s = &s.get_unchecked(1..);
//                             res = val_t.uunchecked_mul(*T::TREE.get_unchecked(s.len()));
//                         } else {
//                             return Err(PIE { kind: IntErrorKind3::InvalidDigit });
//                         };
//                     }
//                     if l32 {
//                         let val = T::from_u128(parse_32_chars(&s)
//                             .map_err(|_| PIE{kind:IntErrorKind3::InvalidDigit })?);
//                         s = &s.get_unchecked(32..);
//                         res= res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
//                     }
//                     if l16 {
//                         let val = T::from_u64(parse_16_chars(&s).map_err(|_| PIE{kind:IntErrorKind3::InvalidDigit })?);
//                         s = &s.get_unchecked(16..);
//                         res = res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
//                     }
//                     if l8 {
//                         let val = T::from_u32(parse_8_chars(&s).map_err(|_| PIE{kind:IntErrorKind3::InvalidDigit })?);
//                         s = &s.get_unchecked(8..);
//                         res = res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
//                     }
//                     if l4 {
//                         let val = T::from_u16(parse_4_chars(&s).map_err(|_| PIE{kind:IntErrorKind3::InvalidDigit })?);
//                         s = &s.get_unchecked(4..);
//                         res = res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
//                     }
//                     if l2 {
//                         let val = T::from_u16(parse_2_chars(&s).map_err(|_| PIE{kind:IntErrorKind3::InvalidDigit })?);
//                         //s = &s.get_unchecked(2..);
//                         res = res.uunchecked_add(val);//T::TREE.get_unchecked(s.len()).uunchecked_mul
//                     }
//                     return if checked.is_none() {
//                         Ok(res)
//                     } else {
//                         checked.unwrap().cchecked_add(res).ok_or_else(|| PIE{kind: IntErrorKind3::InvalidDigit })//PosOverflow})
//                     }
//                 }

//                 if val != b'+' {
//                     if val != b'0' {
//                         if l == T::CHARS {
//                             let val = val.wrapping_sub(b'0');
//                             if val <= 9 {
//                                 let val = T::from_u8(val).cchecked_mul(*T::TREE.get_unchecked(T::CHARS - 1)).ok_or_else(|| PIE{kind: IntErrorKind3::InvalidDigit })?;//PosOverflow})?;
//                                 checked = Some(val);
//                                 s = &s[1..];
//                                 continue;
//                                 //return val.cchecked_add(rest).ok_or_else(|| PIE{kind: IntErrorKind3::InvalidDigit })//PosOverflow})
//                             } else {
//                                 return Err(PIE { kind: IntErrorKind3::InvalidDigit }) //InvalidDigit });
//                             }
//                         } else {
//                             return Err(PIE { kind: IntErrorKind3::InvalidDigit });//PosOverflow });
//                         }
//                     } else {
//                         while val == b'0' {
//                             s = &s[1..];
//                             val = match s.get(0) {
//                                 Some(val) => *val,
//                                 None => return Ok(T::from_u8(0))
//                             }
//                         }
//                         if val == b'+' {
//                             return Err(PIE { kind: IntErrorKind3::InvalidDigit })// Empty });
//                         }
//                     }
//                 } else {
//                     s = &s[1..];
//                     val = match s.get(0) {
//                         Some(val) => {
//                             if *val == b'+' {
//                                 return Err(PIE { kind: IntErrorKind3::InvalidDigit })// Empty });
//                             } else {
//                                 *val
//                             }
//                         }
//                         None => return Err(PIE { kind: IntErrorKind3::InvalidDigit })// Empty });
//                     }
//                 }
//             }
//         } else {
//             return Err(PIE { kind: IntErrorKind3::InvalidDigit })// Empty });
//         }
//     }
// }

// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
// (39 digits!)
// pub fn parse_u128(s: &[u8]) -> Result<u128, PIE> {
//     unsafe {
//         let mut s = s; //.as_bytes();
//         let mut l: usize = s.len();

//         let mut val = match s.get(0) {
//             Some(val) => {
//                 let val = val.wrapping_sub(b'0');
//                 if val <= 9 {
//                     if l == 1 {
//                         return Ok(val as u128);
//                     }
//                     val
//                 } else {
//                     if val == PLUS {
//                         s = &s[1..];
//                         let val = s[0].wrapping_sub(b'0');
//                         if val <= 9 {
//                             l -= 1;
//                             if l == 1 {
//                                 return Ok(val as u128);
//                             }
//                             val
//                         } else {
//                             return Err(PIE { kind: InvalidDigit });
//                         }
//                     } else {
//                         return Err(PIE { kind: InvalidDigit });
//                     }
//                 }
//             }
//             None => return Err(PIE { kind: Empty }),
//         };

//         while val == 0 {
//             s = &s[1..];
//             l -= 1;
//             val = match s.get(0) {
//                 Some(val) => *val,
//                 None => return Ok(0)
//             };
//             val = val.wrapping_sub(b'0');
//             if val <= 9 {
//                 if l == 1 {
//                     return Ok(val as u128);
//                 }
//                 val
//             } else {
//                 return Err(PIE { kind: InvalidDigit });
//             }
//         }
//         if l < 39 {
//             let mut res = 0u128;
//             if l & 1 != 0 {
//                 s = &s.get_unchecked(1..);
//                 res += val as u128 * TENS_U128.get_unchecked(s.len());
//             }
//             if l & 2 != 0 {
//                 let val = s.get_unchecked(0).wrapping_sub(b'0');
//                 let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//                 if (val > 9) | (val2 > 9) {
//                     return Err(PIE { kind: InvalidDigit });
//                 };
//                 res += val as u128 * TENS_U128.get_unchecked(s.len() - 1)
//                     + val2 as u128 * TENS_U128.get_unchecked(s.len() - 2);
//                 s = &s.get_unchecked(2..);
//             }

//             if l & 16 != 0 {
//                 let val16 = parse_16_chars(&s)? as u128;
//                 s = &s.get_unchecked(16..);
//                 res += val16 * TENS_U128.get_unchecked(s.len());
//             }
//             if l & 8 != 0 {
//                 let val = parse_8_chars(&s)? as u128;
//                 s = &s.get_unchecked(8..);
//                 res += val * TENS_U128.get_unchecked(s.len());
//             }
//             if l & 32 != 0 {
//                 let val16 = parse_16_chars(&s)? as u128;
//                 s = &s.get_unchecked(16..);
//                 res += val16 * TENS_U128.get_unchecked(s.len());

//                 // Do the same thing again as a parse_32_chars fn would need 256bits.
//                 let val16 = parse_16_chars(&s)? as u128;
//                 s = &s.get_unchecked(16..);
//                 res += val16 * TENS_U128.get_unchecked(s.len());
//             }
//             if l & 4 != 0 {
//                 res += parse_4_chars(&s)? as u128;
//             }
//             Ok(res)
//         } else {
//             if l == 39 {
//                 //39 = 32 + 4 + 2 + 1
//                 if val <= 3 {
//                     let val = val as u128 * TENS_U128[38];

//                     let val2 = s.get_unchecked(1).wrapping_sub(b'0');
//                     let val3 = s.get_unchecked(2).wrapping_sub(b'0');
//                     if (val2 <= 9) & (val3 <= 9) {
//                         let mut res = val2 as u128 * TENS_U128.get_unchecked(37)
//                             + val3 as u128 * TENS_U128.get_unchecked(36);
//                         s = &s.get_unchecked(3..);

//                         let val16 = parse_16_chars(&s)? as u128;
//                         s = &s.get_unchecked(16..);
//                         res += val16 * TENS_U128.get_unchecked(20);

//                         // Do the same thing again as a parse_32_chars fn would need 256bits.
//                         let val16 = parse_16_chars(&s)? as u128;
//                         s = &s.get_unchecked(16..);
//                         res += val16 * TENS_U128.get_unchecked(4);

//                         res += parse_4_chars(&s)? as u128;

//                         return match val.checked_add(res) {
//                             Some(val) => Ok(val),
//                             None => Err(PIE { kind: PosOverflow }),
//                         };
//                     } else {
//                         return Err(PIE { kind: InvalidDigit });
//                     };
//                 } else {
//                     return Err(PIE { kind: PosOverflow });
//                 }
//             } else {
//                 return Err(PIE { kind: PosOverflow });
//             }
//         }
//     }
// }
