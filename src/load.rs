//! The word loads and alignment tests behind the SWAR parsers, in one place: these are the
//! only reads the proofs cannot see. Aeneas (Rust -> Lean) has no raw pointers and no pointer
//! addresses, so `verification/` leaves them opaque and models each load as the little-endian
//! value of the bytes, which is what the aligned read yields, and `misaligned` as an
//! unspecified `bool`, so every theorem holds whichever alignment branch runs.

/// Whether `s` starts at an address with `bit` set, i.e. is not aligned to `2 * bit`.
#[inline(always)]
pub(crate) fn misaligned(s: &[u8], bit: usize) -> bool {
    s.as_ptr() as usize & bit != 0
}

macro_rules! load {
    ($name:ident, $t:ty) => {
        /// SAFETY: `s` must hold at least `size_of::<$t>()` bytes and be aligned to that.
        #[cfg(target_endian = "little")]
        #[inline(always)]
        pub(crate) unsafe fn $name(s: &[u8]) -> $t {
            const SIZE: usize = core::mem::size_of::<$t>();
            debug_assert!(s.len() >= SIZE);
            debug_assert!((s.as_ptr() as usize).is_multiple_of(SIZE));
            unsafe { *(s.as_ptr() as *const $t) }
        }
    };
}

load!(load_u16, u16);
load!(load_u32, u32);
load!(load_u64, u64);
load!(load_u128, u128);
