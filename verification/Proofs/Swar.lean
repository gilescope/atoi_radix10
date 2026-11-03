import Proofs.Bytes

/-!
The SWAR chunk parsers (`src/lib.rs`): `parse_N_chars s` reads `N` bytes and returns their
decimal value exactly when every byte is an ASCII digit, and `Err(InvalidDigit)` otherwise.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- `b` is an ASCII digit. -/
def isDigit (b : U8) : Prop := 0x30 ≤ b.val ∧ b.val ≤ 0x39

/-- The decimal value of a list of ASCII digits, most significant first. -/
def decimal : List U8 → Nat
  | [] => 0
  | b :: bs => (b.val - 0x30) * 10 ^ bs.length + decimal bs

/-- The first two bytes of a slice, as a two-digit number. -/
theorem decimal_take_two (l : List U8) (h : 2 ≤ l.length) :
    decimal (l.take 2) = (l[0].val - 48) * 10 + (l[1].val - 48) := by
  match l, h with
  | b0 :: b1 :: _, _ => simp [decimal]

end atoi_radix10

namespace atoi_radix10

/-- The arithmetic of `parse_2_chars` on the two bytes `b0 b1` of its word, as plain naturals:
the result fits `u16`; the test passes exactly when both bytes are digits; and then the result
is their decimal value. The names follow the extracted code. -/
theorem swar2 {b0 b1 chunk ch i2 i3 i4 i5 i6 i7 i8 res i9 i10 i11 : ℕ}
    (hb0 : b0 < 256) (hb1 : b1 < 256)
    (hchunk : chunk = (2 ^ 8 * b1 + b0) ^^^ 12336)
    (hch : ch = (chunk + 30326) % 65536)
    (hi2 : i2 = chunk &&& 15) (hi3 : i3 = i2 <<< 1 % 65536)
    (hi4 : i4 = chunk &&& 15) (hi5 : i5 = i4 <<< 3 % 65536)
    (hi6 : i6 = i3 + i5) (hi7 : i7 = chunk &&& 3840) (hi8 : i8 = i7 >>> 8)
    (hres : res = i6 + i8)
    (hi9 : i9 = chunk &&& 61680) (hi10 : i10 = ch &&& 32896) (hi11 : i11 = i9 ||| i10) :
    i6 + i8 ≤ 65535 ∧
      (i11 = 0 ↔ (48 ≤ b0 ∧ b0 ≤ 57) ∧ (48 ≤ b1 ∧ b1 ≤ 57)) ∧
      (i11 = 0 → res = (b0 - 48) * 10 + (b1 - 48)) := by
  -- the word after `^ 0x3030`, byte by byte
  have h48 : (48 : ℕ) < 2 ^ 8 := by norm_num
  have hchunk' : chunk = 2 ^ 8 * (b1 ^^^ 48) + (b0 ^^^ 48) := by
    rw [hchunk, show (12336 : ℕ) = 2 ^ 8 * 48 + 48 by norm_num, xor_split hb0 h48]
  set c0 := b0 ^^^ 48 with hc0
  set c1 := b1 ^^^ 48 with hc1
  have hc0lt : c0 < 2 ^ 8 := Nat.xor_lt_two_pow hb0 h48
  have hc1lt : c1 < 2 ^ 8 := Nat.xor_lt_two_pow hb1 h48
  -- the lane extractions
  have hi2' : i2 = c0 &&& 15 := by
    rw [hi2, hchunk', show (15 : ℕ) = 2 ^ 8 * 0 + 15 by norm_num, land_split hc0lt (by norm_num),
      Nat.and_zero]; simp
  have hi4' : i4 = c0 &&& 15 := by rw [hi4, ← hi2, hi2']
  have hi7' : i7 = 2 ^ 8 * (c1 &&& 15) := by
    rw [hi7, hchunk', show (3840 : ℕ) = 2 ^ 8 * 15 + 0 by norm_num, land_split hc0lt (by norm_num),
      Nat.and_zero, Nat.add_zero]
  have hi9' : i9 = 2 ^ 8 * (c1 &&& 240) + (c0 &&& 240) := by
    rw [hi9, hchunk', show (61680 : ℕ) = 2 ^ 8 * 240 + 240 by norm_num,
      land_split hc0lt (by norm_num)]
  have hm0 : c0 &&& 15 ≤ 15 := Nat.and_le_right
  have hm1 : c1 &&& 15 ≤ 15 := Nat.and_le_right
  have hi3' : i3 = 2 * (c0 &&& 15) := by
    rw [hi3, hi2', Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  have hi5' : i5 = 8 * (c0 &&& 15) := by
    rw [hi5, hi4', Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  have hi8' : i8 = c1 &&& 15 := by
    rw [hi8, hi7', Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by norm_num)]
  have hres' : res = 10 * (c0 &&& 15) + (c1 &&& 15) := by rw [hres, hi6, hi3', hi5', hi8']; ring
  refine ⟨by rw [hi6, hi3', hi5', hi8']; omega, ?_, ?_⟩
  -- the test: high nibbles clear, then `+ 0x76` does not reach bit 7
  · have hz : i11 = 0 ↔ (c0 &&& 240 = 0 ∧ c1 &&& 240 = 0) ∧ i10 = 0 := by
      rw [hi11, Nat.or_eq_zero_iff, hi9']; omega
    rw [hz]
    constructor
    · rintro ⟨⟨h0, h1⟩, h10⟩
      have hc0s := byte_hi_zero c0 hc0lt h0
      have hc1s := byte_hi_zero c1 hc1lt h1
      have hch' : ch = 2 ^ 8 * (c1 + 118) + (c0 + 118) := by
        rw [hch, hchunk', Nat.mod_eq_of_lt (by omega)]; ring
      rw [hi10, hch', show (32896 : ℕ) = 2 ^ 8 * 128 + 128 by norm_num,
        land_split (by omega) (by norm_num)] at h10
      have h10' : (c0 + 118) &&& 128 = 0 ∧ (c1 + 118) &&& 128 = 0 := by omega
      have d0 := (byte_lo_test c0 hc0s).mp h10'.1
      have d1 := (byte_lo_test c1 hc1s).mp h10'.2
      exact ⟨(byte_xor48 b0 hb0).mp d0, (byte_xor48 b1 hb1).mp d1⟩
    · rintro ⟨⟨hb0l, hb0u⟩, ⟨hb1l, hb1u⟩⟩
      obtain ⟨m0, l0⟩ := byte_digit_masks b0 hb0 hb0l hb0u
      obtain ⟨m1, l1⟩ := byte_digit_masks b1 hb1 hb1l hb1u
      have hc0s := byte_hi_zero c0 hc0lt m0
      have hc1s := byte_hi_zero c1 hc1lt m1
      have hch' : ch = 2 ^ 8 * (c1 + 118) + (c0 + 118) := by
        rw [hch, hchunk', Nat.mod_eq_of_lt (by omega)]; ring
      refine ⟨⟨m0, m1⟩, ?_⟩
      rw [hi10, hch', show (32896 : ℕ) = 2 ^ 8 * 128 + 128 by norm_num,
        land_split (by omega) (by norm_num), l0, l1]
      norm_num
  -- the value: with the high nibbles clear, `& 0xf` is the identity
  · intro hv
    have hz : i11 = 0 ↔ (c0 &&& 240 = 0 ∧ c1 &&& 240 = 0) ∧ i10 = 0 := by
      rw [hi11, Nat.or_eq_zero_iff, hi9']; omega
    obtain ⟨⟨h0, h1⟩, h10⟩ := hz.mp hv
    have hc0s := byte_hi_zero c0 hc0lt h0
    have hc1s := byte_hi_zero c1 hc1lt h1
    have hch' : ch = 2 ^ 8 * (c1 + 118) + (c0 + 118) := by
      rw [hch, hchunk', Nat.mod_eq_of_lt (by omega)]; ring
    rw [hi10, hch', show (32896 : ℕ) = 2 ^ 8 * 128 + 128 by norm_num,
      land_split (by omega) (by norm_num)] at h10
    have h10' : (c0 + 118) &&& 128 = 0 ∧ (c1 + 118) &&& 128 = 0 := by omega
    have d0 := (byte_lo_test c0 hc0s).mp h10'.1
    have d1 := (byte_lo_test c1 hc1s).mp h10'.2
    obtain ⟨hb0l, hb0u⟩ := (byte_xor48 b0 hb0).mp d0
    obtain ⟨hb1l, hb1u⟩ := (byte_xor48 b1 hb1).mp d1
    rw [hres', byte_and15 c0 hc0s, byte_and15 c1 hc1s, hc0, hc1, byte_xor48_val b0 hb0 hb0l hb0u,
      byte_xor48_val b1 hb1 hb1l hb1u]
    ring

/-- The partial sums of `parse_2_chars` fit `u16`: the digit lanes are nibbles. -/
theorem swar2_bound {b0 b1 chunk i2 i3 i4 i5 i6 i7 i8 : ℕ} (hb0 : b0 < 256)
    (hchunk : chunk = (2 ^ 8 * b1 + b0) ^^^ 12336)
    (hi2 : i2 = chunk &&& 15) (hi3 : i3 = i2 <<< 1 % 65536)
    (hi4 : i4 = chunk &&& 15) (hi5 : i5 = i4 <<< 3 % 65536)
    (hi6 : i6 = i3 + i5) (hi7 : i7 = chunk &&& 3840) (hi8 : i8 = i7 >>> 8) :
    i3 + i5 ≤ 65535 ∧ i6 + i8 ≤ 65535 := by
  have h48 : (48 : ℕ) < 2 ^ 8 := by norm_num
  have hchunk' : chunk = 2 ^ 8 * (b1 ^^^ 48) + (b0 ^^^ 48) := by
    rw [hchunk, show (12336 : ℕ) = 2 ^ 8 * 48 + 48 by norm_num, xor_split hb0 h48]
  have hc0lt : b0 ^^^ 48 < 2 ^ 8 := Nat.xor_lt_two_pow hb0 h48
  have hi2' : i2 = (b0 ^^^ 48) &&& 15 := by
    rw [hi2, hchunk', show (15 : ℕ) = 2 ^ 8 * 0 + 15 by norm_num, land_split hc0lt (by norm_num),
      Nat.and_zero]; simp
  have hi7' : i7 = 2 ^ 8 * ((b1 ^^^ 48) &&& 15) := by
    rw [hi7, hchunk', show (3840 : ℕ) = 2 ^ 8 * 15 + 0 by norm_num, land_split hc0lt (by norm_num),
      Nat.and_zero, Nat.add_zero]
  have hm0 : (b0 ^^^ 48) &&& 15 ≤ 15 := Nat.and_le_right
  have hm1 : (b1 ^^^ 48) &&& 15 ≤ 15 := Nat.and_le_right
  have hi8' : i8 = (b1 ^^^ 48) &&& 15 := by
    rw [hi8, hi7', Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hi6, hi3, hi5, hi4, ← hi2, hi2', hi8', Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `parse_2_chars`: on a slice of at least two bytes, `Ok` of their decimal value exactly when
both are ASCII digits, `Err(InvalidDigit)` otherwise. -/
theorem parse_2_chars_spec (s : Slice U8) (h : 2 ≤ s.val.length) :
    parse_2_chars s ⦃ r =>
      match r with
      | .Ok v => isDigit s.val[0] ∧ isDigit s.val[1] ∧ v.val = decimal (s.val.take 2)
      | .Err e => ¬ (isDigit s.val[0] ∧ isDigit s.val[1]) ∧ e.kind = .InvalidDigit ⦄ := by
  have hb0 : s.val[0].val < 256 := by scalar_tac
  have hb1 : s.val[1].val < 256 := by scalar_tac
  have hle := leBytes_take_two s.val h
  have hdec := decimal_take_two s.val h
  have hsize : U16.size = 65536 := by simp [U16.size_def, U16.numBits_def]
  unfold parse_2_chars
  step*
  all_goals
    rw [hle] at i1_post
    simp at chunk_post i2_post i3_post i4_post i5_post
    rw [hsize] at i3_post i5_post
    have hchunk := chunk_post
    rw [i1_post] at hchunk
  -- the overflow checks: `i3 + i5`, then `i6 + i8`
  all_goals first
    | (rw [U16.max_eq]
       exact (swar2_bound hb0 hchunk i2_post i3_post i4_post i5_post rfl rfl rfl).1)
    | (simp at i7_post
       rw [U16.max_eq]
       exact (swar2_bound hb0 hchunk i2_post i3_post i4_post i5_post i6_post i7_post i8_post).2)
    | skip
  all_goals
    simp at i7_post i9_post i10_post i11_post
    have hch : ch.val = (chunk.val + 30326) % 65536 := by
      rw [ch_post, core.num.U16.wrapping_add_val_eq, UScalar.size_UScalarTyU16, hsize]; simp
    obtain ⟨hmax, hiff, hval⟩ := swar2 hb0 hb1 hchunk hch i2_post i3_post i4_post i5_post i6_post
      i7_post i8_post res_post i9_post i10_post i11_post
  case h1 =>
    have hz : i11.val = 0 := by rw [‹i11 = 0#u16›]; simp
    obtain ⟨d0, d1⟩ := hiff.mp hz
    exact ⟨d0, d1, by rw [hval hz, hdec]⟩
  case h2 =>
    intro ⟨d0, d1⟩
    apply ‹¬ i11 = 0#u16›
    apply UScalar.eq_of_val_eq
    rw [hiff.mpr ⟨d0, d1⟩]; simp

end atoi_radix10
