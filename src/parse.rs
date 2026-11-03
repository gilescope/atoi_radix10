use super::{parse_digits, IntErrorKind, ParseIntErrorPublic, MINUS, PLUS};
use core::ops::{Add, Mul, Sub};

macro_rules! likely {
    ($e:expr) => {
        $e
        //TODO: use core::intrinsics::likely($e) when stable
    };
}

macro_rules! unlikely {
    ($e:expr) => {
        $e
        //TODO: use core::intrinsics::unlikely($e) when stable
    };
}

type Pie = ParseIntErrorPublic;

#[doc(hidden)]
pub trait FromStrRadixHelper:
    PartialOrd + Copy + Add<Output = Self> + Mul<Output = Self> + Sub<Output = Self> + 'static
{
    const MIN: Self;
    const BITS: u32;
    /// Number of digits in `Self::MAX`.
    const CHARS: usize;
    /// Most significant digit of `Self::MAX` (or of `-Self::MIN` when signed).
    const FIRST_SIG: u8;
    /// `10^(CHARS - 1)`: the place value of the most significant digit.
    const TOP: Self;
    fn from_u128(u: u128) -> Self;
    fn from_u64(u: u64) -> Self;
    fn from_u32(u: u32) -> Self;
    fn from_u16(u: u16) -> Self;
    fn from_u8(u: u8) -> Self;

    fn mul_checked(&self, other: Self) -> Option<Self>;
    fn sub_checked(&self, other: Self) -> Option<Self>;
    fn add_checked(&self, other: Self) -> Option<Self>;
}

macro_rules! doit {
    ($($t:ty,$chars:literal,$first_sig:literal,$top:literal)*) => ($(impl FromStrRadixHelper for $t {
        const MIN: Self = Self::MIN;
        const BITS: u32 = Self::BITS;
        const CHARS: usize = $chars;
        const FIRST_SIG: u8 = $first_sig;
        const TOP: Self = $top;
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
        fn mul_checked(&self, other: Self) -> Option<Self> {
            Self::checked_mul(*self, other as Self)
        }
        #[inline(always)]
        fn sub_checked(&self, other: Self) -> Option<Self> {
            Self::checked_sub(*self, other as Self)
        }
        #[inline(always)]
        fn add_checked(&self, other: Self) -> Option<Self> {
            Self::checked_add(*self, other as Self)
        }
    })*)
}

doit! {
    i8,3,1,100
    i16,5,3,10_000
    i32,10,2,1_000_000_000
    i64,19,9,1_000_000_000_000_000_000
    i128,39,1,100_000_000_000_000_000_000_000_000_000_000_000_000
    u8,3,2,100
    u16,5,6,10_000
    u32,10,4,1_000_000_000
    u64,20,1,10_000_000_000_000_000_000
    u128,39,3,100_000_000_000_000_000_000_000_000_000_000_000_000
}

#[cfg(target_pointer_width = "16")] //E.g. msp430-none-elf micro-controller.
doit! {
    isize,5,3,10_000
    usize,5,6,10_000
}

#[cfg(target_pointer_width = "32")]
doit! {
    isize,10,2,1_000_000_000
    usize,10,4,1_000_000_000
}

#[cfg(target_pointer_width = "64")]
doit! {
    isize,19,9,1_000_000_000_000_000_000
    usize,20,1,10_000_000_000_000_000_000
}

// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
// (39 digits!)
#[doc(hidden)]
pub fn parse_challenger<T>(s: &[u8]) -> Result<T, Pie>
where
    T: FromStrRadixHelper,
{
    parse(s)
}

// u128: 0 to 340_282_366_920_938_463_463_374_607_431_768_211_455
// (39 digits!)

macro_rules! invalid {
    () => {
        Pie {
            kind: IntErrorKind::InvalidDigit,
        }
    };
}
macro_rules! empty {
    () => {
        Pie {
            kind: IntErrorKind::Empty,
        }
    };
}

macro_rules! pos_overflow {
    () => {
        Pie {
            kind: IntErrorKind::PosOverflow,
        }
    };
}

macro_rules! neg_overflow {
    () => {
        Pie {
            kind: IntErrorKind::NegOverflow,
        }
    };
}

/// Parses a UTF8 &str as a number.
///
/// It has exactly the same semantics as `std::str::parse`,
/// but faster. (compiled with nightly,simd features
/// and target native cpu will get the absolute fastest result.)
///
/// Positives are slightly faster than negatives when parsing and
/// if you don't need to put a leading `+` then that will be faster too.
/// # Examples
///
/// ```rust
/// let s = "+000123";
/// assert_eq!(atoi_radix10::parse_from_str(s), Ok(123));
/// ```
#[inline(always)]
pub fn parse_from_str<T: FromStrRadixHelper, S: AsRef<str>>(s: S) -> Result<T, Pie> {
    parse(s.as_ref().as_bytes())
}

/// Parses a UTF8 &[u8] slice as a number.
///
/// Takes a `&[u8]` because any non-utf/non-ascii will fail parsing as an integer.
///
/// It has exactly the same semantics as `std::str::parse`,
/// but faster.
///
/// Positives are slightly faster than negatives when parsing and
/// if you don't need to put a leading `+` then that will be faster too.
///
/// # Examples
///
/// ```rust
/// let s: String = "+000123".into();
/// assert_eq!(atoi_radix10::parse::<u8>(s.as_bytes()), Ok(123));
/// ```
#[inline]
pub fn parse<T>(mut s: &[u8]) -> Result<T, Pie>
where
    T: FromStrRadixHelper,
{
    let is_signed_ty = T::from_u32(0) > T::MIN;
    let first = match s.first() {
        Some(&c) => c,
        None => return Err(empty!()),
    };
    let mut negative = false;
    if unlikely!(first.wrapping_sub(b'0') > 9) {
        if first == PLUS.wrapping_add(b'0') || (is_signed_ty && first == MINUS.wrapping_add(b'0')) {
            negative = is_signed_ty && first == MINUS.wrapping_add(b'0');
            s = &s[1..];
            match s.first() {
                Some(&c) if c.wrapping_sub(b'0') <= 9 => {}
                Some(_) => return Err(invalid!()),
                None => return Err(empty!()),
            }
        } else {
            return Err(invalid!());
        }
    }
    parse_magnitude(s, negative)
}

/// `s` is non-empty and starts with a digit.
#[inline(always)]
fn parse_magnitude<T>(s: &[u8], negative: bool) -> Result<T, Pie>
where
    T: FromStrRadixHelper,
{
    let l = s.len();
    if likely!(l < T::CHARS) {
        // Short enough that it cannot overflow.
        let v = parse_digits::<T>(s)?;
        return Ok(if negative { T::from_u8(0) - v } else { v });
    }
    if l == T::CHARS {
        let d = s[0].wrapping_sub(b'0');
        if likely!(d <= T::FIRST_SIG) {
            // Peel the most significant digit off; the rest can't overflow,
            // and `d <= FIRST_SIG` keeps `head` in range too.
            let head = T::from_u8(d) * T::TOP;
            let rest = parse_digits::<T>(&s[1..])?;
            return if negative {
                (T::from_u8(0) - rest)
                    .sub_checked(head)
                    .ok_or(neg_overflow!())
            } else {
                head.add_checked(rest).ok_or(pos_overflow!())
            };
        }
    }
    parse_long(s, negative)
}

/// `s` starts with a digit, has at least `T::CHARS` bytes and isn't the
/// exactly-`CHARS`-digits-and-fits case: it either has leading zeros or it
/// overflows.
#[inline(never)]
fn parse_long<T>(s: &[u8], negative: bool) -> Result<T, Pie>
where
    T: FromStrRadixHelper,
{
    if s[0] != b'0' {
        return Err(if negative {
            neg_overflow!()
        } else {
            pos_overflow!()
        });
    }
    let zeros = s.iter().take_while(|&&c| c == b'0').count();
    let s = &s[zeros..];
    match s.first() {
        None => Ok(T::from_u8(0)),
        Some(&c) if c.wrapping_sub(b'0') <= 9 => parse_magnitude(s, negative),
        Some(_) => Err(invalid!()),
    }
}
