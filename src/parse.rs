use super::{
    parse_16_chars, parse_2_chars, parse_32_chars, parse_4_chars, parse_8_chars, trees::*,
    IntErrorKind3, ParseIntError3,
};

type PIE = ParseIntError3;

#[doc(hidden)]
pub(crate) trait FromStrRadixHelper: PartialOrd + Copy + 'static {
    const MIN: Self;
    const BITS: u32;
    const TREE: &'static [Self];
    const CHARS: usize;
    fn from_u128(u: u128) -> Self;
    fn from_u64(u: u64) -> Self;
    fn from_u32(u: u32) -> Self;
    fn from_u16(u: u16) -> Self;
    fn from_u8(u: u8) -> Self;

    fn cchecked_mul(&self, other: Self) -> Option<Self>;
    fn cchecked_sub(&self, other: Self) -> Option<Self>;
    fn cchecked_add(&self, other: Self) -> Option<Self>;
    unsafe fn uunchecked_mul(&self, other: Self) -> Self;
    unsafe fn uunchecked_sub(&self, other: Self) -> Self;
    unsafe fn uunchecked_add(&self, other: Self) -> Self;
}

macro_rules! doit {
    ($($t:ty,$tr:expr,$chars:literal)*) => ($(impl FromStrRadixHelper for $t {
        const MIN: Self = Self::MIN;
        const BITS: u32 = Self::BITS;
        const TREE: &'static[Self] = $tr;
        const CHARS: usize = $chars;
        #[inline(always)]
        fn from_u128(u: u128) -> Self { u as Self }
        #[inline(always)]
        fn from_u64(u: u64) -> Self { u as Self }
        #[inline(always)]
        fn from_u32(u: u32) -> Self { u as Self }
        #[inline(always)]
        fn from_u16(u: u16) -> Self { u as Self }
        #[inline(always)]
        fn from_u8(u: u8) -> Self { u as Self }
        #[inline(always)]
        fn cchecked_mul(&self, other: Self) -> Option<Self> {
            Self::checked_mul(*self, other as Self)
        }
        #[inline(always)]
        fn cchecked_sub(&self, other: Self) -> Option<Self> {
            Self::checked_sub(*self, other as Self)
        }
        #[inline(always)]
        fn cchecked_add(&self, other: Self) -> Option<Self> {
            Self::checked_add(*self, other as Self)
        }
        #[inline(always)]
        unsafe fn uunchecked_mul(&self, other: Self) -> Self {
            Self::unchecked_mul(*self, other as Self)
        }
        #[inline(always)]
        unsafe fn uunchecked_sub(&self, other: Self) -> Self {
            Self::unchecked_sub(*self, other as Self)
        }
        #[inline(always)]
        unsafe fn uunchecked_add(&self, other: Self) -> Self {
            Self::unchecked_add(*self, other as Self)
        }
    })*)
}
doit! { i8,TENS_I8,3 i16,TENS_I16,5 i32,TENS_I32,10 i64,TENS_I64,20 i128,TENS_I128,39 isize,TENS_ISIZE,20 u8,TENS_U8,3 u16,TENS_U16,5 u32,TENS_U32,10 u64,TENS_U64,20 u128,TENS_U128,39 usize,TENS_USIZE,20 }

/// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
/// (39 digits!)

pub(crate) fn parse<T>(mut s: &[u8]) -> Result<T, PIE>
where
    T: FromStrRadixHelper,
{
    let is_signed_ty = T::from_u32(0) > T::MIN;
    unsafe {
        let mut checked: Option<T> = None;
        if let Some(val) = s.get(0) {
            let mut val = *val;
            if val == b'-' && is_signed_ty {
                s = &s[1..];
                match s.get(0) {
                    Some(val) => {
                        let mut val = *val;
                        loop {
                            let l = s.len();
                            let mut res = T::from_u8(0);
                            if std::intrinsics::likely(l < T::CHARS) {
                                let l1_ = l & 1_ != 0 && T::BITS >= 4__;
                                let l2_ = l & 2_ != 0 && T::BITS >= 8__;
                                let l4_ = l & 4_ != 0 && T::BITS >= 16_;
                                let l8_ = l & 8_ != 0 && T::BITS >= 32_;
                                let l16 = l & 16 != 0 && T::BITS >= 64_;
                                let l32 = l & 32 != 0 && T::BITS >= 128;

                                if l1_ {
                                    let val = val.wrapping_sub(b'0');
                                    let val_t = T::from_u8(0).uunchecked_sub(T::from_u8(val));
                                    if std::intrinsics::likely(val <= 9) {
                                        if l == 1 {
                                            return Ok(val_t);
                                        }
                                        s = &s.get_unchecked(1..);
                                        res = val_t.uunchecked_mul(*T::TREE.get_unchecked(s.len()));
                                    } else {
                                        return Err(PIE {
                                            kind: IntErrorKind3::InvalidDigit,
                                        });
                                    };
                                }
                                if l32 {
                                    let val =
                                        T::from_u128(parse_32_chars(&s).map_err(|_| PIE {
                                            kind: IntErrorKind3::InvalidDigit,
                                        })?);
                                    s = &s.get_unchecked(32..);
                                    res = res.uunchecked_sub(
                                        T::TREE.get_unchecked(s.len()).uunchecked_mul(val),
                                    );
                                }
                                if l16 {
                                    let val = T::from_u64(parse_16_chars(&s).map_err(|_| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    })?);
                                    s = &s.get_unchecked(16..);
                                    res = res.uunchecked_sub(
                                        T::TREE.get_unchecked(s.len()).uunchecked_mul(val),
                                    );
                                }
                                if l8_ {
                                    let val = T::from_u32(parse_8_chars(&s).map_err(|_| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    })?);
                                    s = &s.get_unchecked(8..);
                                    res = res.uunchecked_sub(
                                        T::TREE.get_unchecked(s.len()).uunchecked_mul(val),
                                    );
                                }
                                if l4_ {
                                    let val = T::from_u16(parse_4_chars(&s).map_err(|_| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    })?);
                                    s = &s.get_unchecked(4..);
                                    res = res.uunchecked_sub(
                                        T::TREE.get_unchecked(s.len()).uunchecked_mul(val),
                                    );
                                }
                                if l2_ {
                                    let val = T::from_u16(parse_2_chars(&s).map_err(|_| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    })?);
                                    //s = &s.get_unchecked(2..);
                                    res = res.uunchecked_sub(val); //T::TREE.get_unchecked(s.len()).uunchecked_mul
                                }
                                return if checked.is_none() {
                                    Ok(res)
                                } else {
                                    checked.unwrap().cchecked_sub(res).ok_or_else(|| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    }) //PosOverflow})
                                };
                            }

                            if val != b'0' {
                                if l == T::CHARS {
                                    let val = val.wrapping_sub(b'0');
                                    if val <= 9 {
                                        let val = T::from_u8(val)
                                            .cchecked_mul(*T::TREE.get_unchecked(T::CHARS - 1))
                                            .ok_or_else(|| PIE {
                                                kind: IntErrorKind3::InvalidDigit,
                                            })?; //PosOverflow})?;
                                        checked = Some(val);
                                        s = &s[1..];
                                        continue;
                                        //return val.cchecked_add(rest).ok_or_else(|| PIE{kind: IntErrorKind3::InvalidDigit })//PosOverflow})
                                    } else {
                                        return Err(PIE {
                                            kind: IntErrorKind3::InvalidDigit,
                                        }); //InvalidDigit });
                                    }
                                } else {
                                    return Err(PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    }); //PosOverflow });
                                }
                            } else {
                                while val == b'0' {
                                    s = &s[1..];
                                    val = match s.get(0) {
                                        Some(val) => *val,
                                        None => return Ok(T::from_u8(0)),
                                    }
                                }
                                if val == b'+' {
                                    return Err(PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    }); // Empty });
                                }
                            }
                        }
                    }
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })
                    } // Empty });
                }
            }
            loop {
                let l = s.len();
                // let val1 = val.wrapping_sub(b'0');
                // if l == 1 && val1 <= 9 {
                //     return Ok(T::from_u8(val1));
                // }

                let mut res = T::from_u8(0);
                if std::intrinsics::likely(val != b'+' && l < T::CHARS) {
                    let l_1 = l & 1_ != 0 && T::BITS >= 4__;
                    let l_2 = l & 2_ != 0 && T::BITS >= 8__;
                    let l_4 = l & 4_ != 0 && T::BITS >= 16_;
                    let l_8 = l & 8_ != 0 && T::BITS >= 32_;
                    let l16 = l & 16 != 0 && T::BITS >= 64_;
                    let l32 = l & 32 != 0 && T::BITS >= 128;

                    if l_1 {
                        let val = val.wrapping_sub(b'0');
                        let val_t = T::from_u8(val);
                        if std::intrinsics::likely(val <= 9) {
                            if l == 1 {
                                return Ok(val_t);
                            }
                            s = &s.get_unchecked(1..);
                            res = val_t.uunchecked_mul(*T::TREE.get_unchecked(s.len()));
                        } else {
                            return Err(PIE {
                                kind: IntErrorKind3::InvalidDigit,
                            });
                        };
                    }
                    if l32 {
                        let val = T::from_u128(parse_32_chars(&s).map_err(|_| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })?);
                        s = &s.get_unchecked(32..);
                        res =
                            res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
                    }
                    if l16 {
                        let val = T::from_u64(parse_16_chars(&s).map_err(|_| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })?);
                        s = &s.get_unchecked(16..);
                        res =
                            res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
                    }
                    if l_8 {
                        let val = T::from_u32(parse_8_chars(&s).map_err(|_| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })?);
                        s = &s.get_unchecked(8..);
                        res =
                            res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
                    }
                    if l_4 {
                        let val = T::from_u16(parse_4_chars(&s).map_err(|_| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })?);
                        s = &s.get_unchecked(4..);
                        res =
                            res.uunchecked_add(T::TREE.get_unchecked(s.len()).uunchecked_mul(val));
                    }
                    if l_2 {
                        let val = T::from_u16(parse_2_chars(&s).map_err(|_| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        })?);
                        //s = &s.get_unchecked(2..);
                        res = res.uunchecked_add(val); //T::TREE.get_unchecked(s.len()).uunchecked_mul
                    }
                    return if checked.is_none() {
                        Ok(res)
                    } else {
                        checked.unwrap().cchecked_add(res).ok_or_else(|| PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        }) //PosOverflow})
                    };
                }

                if val != b'+' {
                    if val != b'0' {
                        if l == T::CHARS {
                            val = val.wrapping_sub(b'0');
                            if val <= 9 {
                                let val_checked = T::from_u8(val)
                                    .cchecked_mul(*T::TREE.get_unchecked(T::CHARS - 1))
                                    .ok_or_else(|| PIE {
                                        kind: IntErrorKind3::InvalidDigit,
                                    })?; //PosOverflow})?;
                                checked = Some(val_checked);
                                s = &s[1..];
                                val = s[0];
                                continue;
                                //return val.cchecked_add(rest).ok_or_else(|| PIE{kind: IntErrorKind3::InvalidDigit })//PosOverflow})
                            } else {
                                return Err(PIE {
                                    kind: IntErrorKind3::InvalidDigit,
                                }); //InvalidDigit });
                            }
                        } else {
                            return Err(PIE {
                                kind: IntErrorKind3::InvalidDigit,
                            }); //PosOverflow });
                        }
                    } else {
                        while val == b'0' {
                            s = &s[1..];
                            val = match s.get(0) {
                                Some(val) => *val,
                                None => return Ok(T::from_u8(0)),
                            }
                        }
                        if val == b'+' {
                            return Err(PIE {
                                kind: IntErrorKind3::InvalidDigit,
                            }); // Empty });
                        }
                    }
                } else {
                    if checked.is_some() {
                        return Err(PIE {
                            kind: IntErrorKind3::InvalidDigit,
                        });
                    }
                    s = &s[1..];
                    val = match s.get(0) {
                        Some(val) => {
                            if *val == b'+' {
                                return Err(PIE {
                                    kind: IntErrorKind3::InvalidDigit,
                                }); // Empty });
                            } else {
                                *val
                            }
                        }
                        None => {
                            return Err(PIE {
                                kind: IntErrorKind3::InvalidDigit,
                            })
                        } // Empty });
                    }
                }
            }
        } else {
            return Err(PIE {
                kind: IntErrorKind3::InvalidDigit,
            }); // Empty });
        }
    }
}

// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
// (39 digits!)
