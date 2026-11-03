import Proofs.Swar

/-!
The reference: `core::num::from_str_radix::<T>(s, 10)`, which `str::parse` calls, written over
the integers for a type whose values are those in `[lo, hi]`. `parse` is specified against it.

Core's rule (library/core/src/num/mod.rs, `from_ascii_radix`): an empty string is `Empty`; a
lone sign is `InvalidDigit`; a leading `+` is skipped, a leading `-` too for a signed type;
then each byte must be a digit (`InvalidDigit` at the first that is not), and the running
value must stay in range after each one (`PosOverflow`, or `NegOverflow` when negative).
Core checks the multiplication and the addition separately, but the accumulator never
changes sign, so one range test after both is the same test.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

abbrev Kind := core.num.error.IntErrorKind

instance : DecidablePred isDigit := fun b => inferInstanceAs (Decidable (0x30 ≤ b.val ∧ b.val ≤ 0x39))

/-- The digits of `s`, folded onto `acc`; `neg` subtracts them. -/
def stdDigits (lo hi : ℤ) (neg : Bool) : ℤ → List U8 → Except Kind ℤ
  | acc, [] => .ok acc
  | acc, b :: bs =>
    if isDigit b then
      let acc' := if neg then acc * 10 - ((b.val : ℤ) - 48) else acc * 10 + ((b.val : ℤ) - 48)
      if lo ≤ acc' ∧ acc' ≤ hi then stdDigits lo hi neg acc' bs
      else .error (if neg then .NegOverflow else .PosOverflow)
    else .error .InvalidDigit

/-- `str::parse::<T>` for a type with values `[lo, hi]` (signed exactly when `lo < 0`). -/
def stdParse (lo hi : ℤ) : List U8 → Except Kind ℤ
  | [] => .error .Empty
  | [b] => if b.val = 43 ∨ b.val = 45 then .error .InvalidDigit else stdDigits lo hi false 0 [b]
  | b :: rest =>
    if b.val = 43 then stdDigits lo hi false 0 rest
    else if b.val = 45 ∧ lo < 0 then stdDigits lo hi true 0 rest
    else stdDigits lo hi false 0 (b :: rest)

/-- The crate's error kind against core's: the same, except that core's `InvalidDigit` may
come back as any kind (the crate reports `Empty` or an overflow on some inputs where core
reports the bad digit; the fuzzer compares `Ok`/`Err` only). -/
def kindLike (k ref : Kind) : Prop := k = ref ∨ ref = .InvalidDigit

/-! Sanity checks against `str::parse`, by computation. -/

deriving instance DecidableEq for Except


example : stdParse 0 255 [] = .error .Empty := by decide +kernel
example : stdParse 0 255 [43#u8] = .error .InvalidDigit := by decide +kernel
example : stdParse 0 255 [45#u8] = .error .InvalidDigit := by decide +kernel
example : stdParse (-128) 127 [45#u8] = .error .InvalidDigit := by decide +kernel
example : stdParse 0 255 [45#u8, 53#u8] = .error .InvalidDigit := by decide +kernel
example : stdParse (-128) 127 [45#u8, 53#u8] = .ok (-5) := by decide +kernel
example : stdParse 0 255 [43#u8, 48#u8, 49#u8, 50#u8] = .ok 12 := by decide +kernel
example : stdParse 0 255 [51#u8, 48#u8, 48#u8] = .error .PosOverflow := by decide +kernel
example : stdParse (-128) 127 [45#u8, 49#u8, 50#u8, 57#u8] = .error .NegOverflow := by decide +kernel
example : stdParse (-128) 127 [45#u8, 49#u8, 50#u8, 56#u8] = .ok (-128) := by decide +kernel
example : stdParse 0 255 [57#u8, 57#u8, 57#u8, 120#u8] = .error .PosOverflow := by decide +kernel
example : stdParse 0 255 [49#u8, 120#u8] = .error .InvalidDigit := by decide +kernel

end atoi_radix10
