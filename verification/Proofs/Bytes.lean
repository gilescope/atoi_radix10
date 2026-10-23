import Proofs.Load

/-!
Bytes inside words. The SWAR parsers treat a word as lanes of bytes, so their bitwise steps
are read lane by lane: a bitwise operation on `2^k·b + a` with `a < 2^k` acts on `a` and `b`
separately, and the per-byte facts the digit test rests on are decided over the 256 bytes.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- A bitwise operation acts independently below and above bit `k`. -/
theorem Nat.bitwise_split (f : Bool → Bool → Bool) (hf : f false false = false) {k a b c d : ℕ}
    (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    Nat.bitwise f (2 ^ k * b + a) (2 ^ k * d + c) =
      2 ^ k * Nat.bitwise f b d + Nat.bitwise f a c := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : Nat.bitwise f a c < 2 ^ k := Nat.bitwise_lt_two_pow ha hc
  rw [Nat.testBit_bitwise hf, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split
  · rw [Nat.testBit_bitwise hf]
  · rw [Nat.testBit_bitwise hf]

theorem land_split {k a b c d : ℕ} (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    (2 ^ k * b + a) &&& (2 ^ k * d + c) = 2 ^ k * (b &&& d) + (a &&& c) :=
  Nat.bitwise_split and rfl ha hc

theorem lor_split {k a b c d : ℕ} (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    (2 ^ k * b + a) ||| (2 ^ k * d + c) = 2 ^ k * (b ||| d) + (a ||| c) :=
  Nat.bitwise_split or rfl ha hc

theorem xor_split {k a b c d : ℕ} (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    (2 ^ k * b + a) ^^^ (2 ^ k * d + c) = 2 ^ k * (b ^^^ d) + (a ^^^ c) :=
  Nat.bitwise_split bne rfl ha hc

/-- The first two bytes of a slice, as a little-endian word. -/
theorem leBytes_take_two (l : List U8) (h : 2 ≤ l.length) :
    leBytes (l.take 2) = 2 ^ 8 * l[1].val + l[0].val := by
  match l, h with
  | b0 :: b1 :: _, _ => simp [leBytes]; ring

/-! ### The digit test, byte by byte

`c = b ^ 0x30`. `c & 0xf0 = 0` says `c < 16`; then `(c + 0x76) & 0x80 = 0` says `c ≤ 9`; and
`c ≤ 9` says `b` is a digit, with `c` its value. Decided over the 256 bytes. -/

theorem byte_hi_zero : ∀ c < 256, c &&& 240 = 0 → c < 16 := by decide +kernel

theorem byte_lo_test : ∀ c < 16, ((c + 118) &&& 128 = 0 ↔ c ≤ 9) := by decide +kernel

theorem byte_and15 : ∀ c < 16, c &&& 15 = c := by decide +kernel

theorem byte_xor48 : ∀ b < 256, (b ^^^ 48 ≤ 9 ↔ 48 ≤ b ∧ b ≤ 57) := by decide +kernel

theorem byte_xor48_val : ∀ b < 256, 48 ≤ b → b ≤ 57 → b ^^^ 48 = b - 48 := by decide +kernel

theorem byte_digit_masks : ∀ b < 256, 48 ≤ b → b ≤ 57 →
    (b ^^^ 48) &&& 240 = 0 ∧ ((b ^^^ 48) + 118) &&& 128 = 0 := by decide +kernel

end atoi_radix10
