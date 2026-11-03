import Proofs.DigitTest
import Proofs.Swar

/-!
`parse_4_chars` (`src/lib.rs`): four bytes, two SWAR steps. With `c_i = b_i ^ 0x30`, the word
`lanes 8 [c0, c1, c2, c3]` is first folded into two-digit lanes `e0 = 10 c0 + c1` and
`e2 = 10 c2 + c3` (bytes 0 and 2), then into `100 e0 + e2`.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- Masks and constants, as lanes. -/
theorem c_30303030 : (808464432 : ℕ) = lanes 8 [48, 48, 48, 48] := by norm_num [lanes]
theorem c_0f000f00 : (251662080 : ℕ) = lanes 8 [0, 15, 0, 15] := by norm_num [lanes]
theorem c_76767676 : (1987475062 : ℕ) = lanes 8 (List.replicate 4 118) := by norm_num [lanes]
theorem c_80808080 : (2155905152 : ℕ) = lanes 8 (List.replicate 4 128) := by norm_num [lanes]
theorem c_000f000f : (983055 : ℕ) = lanes 8 [15, 0, 15, 0] := by norm_num [lanes]
theorem c_f0f0f0f0 : (4042322160 : ℕ) = lanes 8 (List.replicate 4 240) := by norm_num [lanes]
theorem c_00ff0000 : (16711680 : ℕ) = lanes 8 [0, 0, 255, 0] := by norm_num [lanes]

/-- The first fold of `parse_4_chars`, from the word `chunk1 = lanes 8 [c0, c1, c2, c3]` to
`chunk = lanes 8 [10 c0' + c1', 0, 10 c2' + c3', 0]` (`c' = c & 0xf`), with the overflow checks
on the way. -/
theorem swar4_fold {c0 c1 c2 c3 chunk1 i2 lower i4 i5 chunk : ℕ}
    (hc0 : c0 < 2 ^ 8) (hc1 : c1 < 2 ^ 8) (hc2 : c2 < 2 ^ 8) (hc3 : c3 < 2 ^ 8)
    (hchunk1 : chunk1 = lanes 8 [c0, c1, c2, c3])
    (hi2 : i2 = chunk1 &&& 251662080) (hlower : lower = i2 >>> 8)
    (hi4 : i4 = chunk1 &&& 983055) (hi5 : i5 = i4 * 10) (hchunk : chunk = lower + i5) :
    i4 * 10 ≤ 4294967295 ∧ lower + i5 ≤ 4294967295 ∧
      chunk = lanes 8 [10 * (c0 &&& 15) + (c1 &&& 15), 0, 10 * (c2 &&& 15) + (c3 &&& 15), 0] := by
  have hcs : ∀ c ∈ [c0, c1, c2, c3], c < 2 ^ 8 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> assumption
  have h15 : ∀ c, c &&& 15 ≤ 15 := fun c => Nat.and_le_right
  have hi2' : i2 = lanes 8 [0, c1 &&& 15, 0, c3 &&& 15] := by
    rw [hi2, hchunk1, c_0f000f00, lanes_and 8 [c0, c1, c2, c3] [0, 15, 0, 15] hcs (by decide) rfl]
    simp [Nat.and_zero]
  have hlower' : lower = lanes 8 [c1 &&& 15, 0, c3 &&& 15, 0] := by
    have hb : ∀ x ∈ [0, c1 &&& 15, 0, c3 &&& 15], x < 2 ^ 8 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      have := h15 c1; have := h15 c3
      rcases hx with rfl | rfl | rfl | rfl <;> omega
    rw [hlower, hi2', Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 8 = (2 ^ 8) ^ 1 by norm_num,
      lanes_div 8 1 _ hb, ← lanes_snoc_zero]
    rfl
  have hi4' : i4 = lanes 8 [c0 &&& 15, 0, c2 &&& 15, 0] := by
    rw [hi4, hchunk1, c_000f000f, lanes_and 8 [c0, c1, c2, c3] [15, 0, 15, 0] hcs (by decide) rfl]
    simp [Nat.and_zero]
  have hi5' : i5 = lanes 8 [10 * (c0 &&& 15), 0, 10 * (c2 &&& 15), 0] := by
    rw [hi5, Nat.mul_comm, hi4', lanes_mul]; simp
  have hchunk' :
      chunk = lanes 8 [10 * (c0 &&& 15) + (c1 &&& 15), 0, 10 * (c2 &&& 15) + (c3 &&& 15), 0] := by
    rw [hchunk, hlower', hi5',
      lanes_add 8 [c1 &&& 15, 0, c3 &&& 15, 0] [10 * (c0 &&& 15), 0, 10 * (c2 &&& 15), 0] rfl]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, lanes_cons, lanes_nil]
    ring
  refine ⟨?_, ?_, hchunk'⟩
  · rw [← hi5, hi5']; simp only [lanes_cons, lanes_nil]; have := h15 c0; have := h15 c2; omega
  · rw [← hchunk, hchunk']; simp only [lanes_cons, lanes_nil]
    have := h15 c0; have := h15 c1; have := h15 c2; have := h15 c3; omega

/-- The second fold, from `chunk = lanes 8 [e0, 0, e2, 0]` with `e0, e2 < 2^8` to
`chunk2 = 100 e0 + e2`, with the overflow checks on the way. -/
theorem swar4_fold2 {e0 e2 chunk masked m1 m2 m3 i7 i8 r i9 i10 chunk2 : ℕ}
    (he0 : e0 < 2 ^ 8) (he2 : e2 < 2 ^ 8) (hchunk : chunk = lanes 8 [e0, 0, e2, 0])
    (hmasked : masked = chunk % 2 ^ 16)
    (hm1 : m1 = masked <<< 6 % 65536) (hm2 : m2 = masked <<< 5 % 65536)
    (hm3 : m3 = masked <<< 2 % 65536)
    (hi7 : i7 = chunk &&& 16711680) (hi8 : i8 = i7 >>> 16) (hr : r = i8 % 2 ^ 16)
    (hi9 : i9 = r + m1) (hi10 : i10 = i9 + m2) (hchunk2 : chunk2 = i10 + m3) :
    r + m1 ≤ 65535 ∧ i9 + m2 ≤ 65535 ∧ i10 + m3 ≤ 65535 ∧ chunk2 = 100 * e0 + e2 := by
  have hes : ∀ x ∈ [e0, 0, e2, 0], x < 2 ^ 8 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  have hmasked' : masked = e0 := by
    rw [hmasked, hchunk, show (2 : ℕ) ^ 16 = (2 ^ 8) ^ 2 by norm_num, lanes_mod 8 2 _ hes]; simp
  have hi7' : i7 = lanes 8 [0, 0, e2, 0] := by
    rw [hi7, hchunk, c_00ff0000, lanes_and 8 [e0, 0, e2, 0] [0, 0, 255, 0] hes (by decide) rfl]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, Nat.and_zero,
      byte_and255 e2 he2]
  have hi8' : i8 = e2 := by
    rw [hi8, hi7', Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 16 = (2 ^ 8) ^ 2 by norm_num,
      lanes_div 8 2 [0, 0, e2, 0] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega)]
    simp
  have hr' : r = e2 := by rw [hr, hi8', Nat.mod_eq_of_lt (by omega)]
  have hm1' : m1 = 64 * e0 := by
    rw [hm1, hmasked', Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  have hm2' : m2 = 32 * e0 := by
    rw [hm2, hmasked', Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  have hm3' : m3 = 4 * e0 := by
    rw [hm3, hmasked', Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  refine ⟨by omega, by omega, by omega, by omega⟩

end atoi_radix10

namespace atoi_radix10

/-- `isDigit b` as the parsers test it: `b ^ 0x30 ≤ 9`. -/
theorem isDigit_iff_xor (b : U8) : isDigit b ↔ b.val ^^^ 48 ≤ 9 := by
  have hb : b.val < 256 := by scalar_tac
  rw [byte_xor48 b.val hb]; rfl

/-- The digit's value. -/
theorem isDigit_xor_val (b : U8) (hd : isDigit b) : b.val ^^^ 48 = b.val - 48 := by
  have hb : b.val < 256 := by scalar_tac
  exact byte_xor48_val b.val hb hd.1 hd.2

/-- `parse_4_chars`: on a slice of at least four bytes, `Ok` of their decimal value exactly when
all four are ASCII digits, `Err(InvalidDigit)` otherwise. -/
theorem parse_4_chars_spec (s : Slice U8) (h : 4 ≤ s.val.length) :
    parse_4_chars s ⦃ r =>
      match r with
      | .Ok v => (∀ b ∈ s.val.take 4, isDigit b) ∧ v.val = decimal (s.val.take 4)
      | .Err e => ¬ (∀ b ∈ s.val.take 4, isDigit b) ∧ e.kind = .InvalidDigit ⦄ := by
  -- the four bytes
  obtain ⟨l, hl⟩ : ∃ l, s.val = l := ⟨_, rfl⟩
  rw [hl] at h
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;> simp at h
  have hlen : 4 ≤ s.val.length := by rw [hl]; simp
  have hb0 : b0.val < 2 ^ 8 := by scalar_tac
  have hb1 : b1.val < 2 ^ 8 := by scalar_tac
  have hb2 : b2.val < 2 ^ 8 := by scalar_tac
  have hb3 : b3.val < 2 ^ 8 := by scalar_tac
  have hbs : ∀ x ∈ [b0.val, b1.val, b2.val, b3.val], x < 2 ^ 8 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hle : leBytes (s.val.take 4) = lanes 8 [b0.val, b1.val, b2.val, b3.val] := by
    rw [hl]; simp [leBytes_eq_lanes]
  have hdec : decimal (s.val.take 4) =
      ((b0.val - 48) * 10 + (b1.val - 48)) * 100 + ((b2.val - 48) * 10 + (b3.val - 48)) := by
    rw [hl]; simp [decimal]; ring
  have hdig : (∀ b ∈ s.val.take 4, isDigit b) ↔
      isDigit b0 ∧ isDigit b1 ∧ isDigit b2 ∧ isDigit b3 := by
    rw [hl]; simp
  -- the bytes after `^ 0x30`
  set c0 := b0.val ^^^ 48 with hc0
  set c1 := b1.val ^^^ 48 with hc1
  set c2 := b2.val ^^^ 48 with hc2
  set c3 := b3.val ^^^ 48 with hc3
  have h48 : (48 : ℕ) < 2 ^ 8 := by norm_num
  have hc0lt : c0 < 2 ^ 8 := Nat.xor_lt_two_pow hb0 h48
  have hc1lt : c1 < 2 ^ 8 := Nat.xor_lt_two_pow hb1 h48
  have hc2lt : c2 < 2 ^ 8 := Nat.xor_lt_two_pow hb2 h48
  have hc3lt : c3 < 2 ^ 8 := Nat.xor_lt_two_pow hb3 h48
  have hcs : ∀ c ∈ [c0, c1, c2, c3], c < 2 ^ 8 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> assumption
  -- the digit test, on these bytes
  have htest := digit_test [c0, c1, c2, c3] hcs
  have hdigc : (∀ c ∈ [c0, c1, c2, c3], c ≤ 9) ↔ (∀ b ∈ s.val.take 4, isDigit b) := by
    rw [hdig, isDigit_iff_xor, isDigit_iff_xor, isDigit_iff_xor, isDigit_iff_xor]; simp
    rw [hc0, hc1, hc2, hc3]
  have hsize32 : U32.size = (2 ^ 8) ^ 4 := by simp [U32.size_def, U32.numBits_def]
  unfold parse_4_chars
  step*
  all_goals
    simp only [parse_4_chars.ASCII_ZEROS] at chunk1_post
    try simp only [parse_4_chars.MASK_HI] at i6_post
    simp at chunk1_post i2_post i4_post
    rw [hle] at i1_post
    have hchunk1 : chunk1.val = lanes 8 [c0, c1, c2, c3] := by
      rw [chunk1_post, i1_post, c_30303030,
        lanes_xor 8 [b0.val, b1.val, b2.val, b3.val] [48, 48, 48, 48] hbs (by decide) rfl]
      rfl
  -- the overflow checks of the first fold
  all_goals first
    | (rw [U32.max_eq]
       exact (swar4_fold hc0lt hc1lt hc2lt hc3lt hchunk1 i2_post lower_digits_post i4_post rfl
         rfl).1)
    | (rw [U32.max_eq]
       exact (swar4_fold hc0lt hc1lt hc2lt hc3lt hchunk1 i2_post lower_digits_post i4_post
         i5_post rfl).2.1)
    | skip
  -- the main path
  obtain ⟨-, -, hchunk⟩ := swar4_fold hc0lt hc1lt hc2lt hc3lt hchunk1 i2_post lower_digits_post
    i4_post i5_post chunk_post
  simp at i6_post
  have hi6 : i6.val = lanes 8 [c0, c1, c2, c3] &&& lanes 8 (List.replicate 4 240) := by
    rw [i6_post, hchunk1, c_f0f0f0f0]
  have hsum : sum.val = ((lanes 8 [c0, c1, c2, c3] + lanes 8 (List.replicate 4 118)) % (2 ^ 8) ^ 4)
      &&& lanes 8 (List.replicate 4 128) := by
    simp at sum_post
    have h76 : (1987475062#u32 : U32).val = 1987475062 := by simp
    rw [sum_post, i3_post, core.num.U32.wrapping_add_val_eq, UScalar.size_UScalarTyU32, hsize32,
      hchunk1, h76, c_76767676, c_80808080]
  have htest' := htest
  have hl4 : [c0, c1, c2, c3].length = 4 := rfl
  rw [hl4, ← hi6, ← hsum, hdigc] at htest'
  -- the value lanes stay bytes
  have h15 : ∀ c, c &&& 15 ≤ 15 := fun c => Nat.and_le_right
  have he0 : 10 * (c0 &&& 15) + (c1 &&& 15) < 2 ^ 8 := by have := h15 c0; have := h15 c1; omega
  have he2 : 10 * (c2 &&& 15) + (c3 &&& 15) < 2 ^ 8 := by have := h15 c2; have := h15 c3; omega
  have hmasked : masked.val = chunk.val % 2 ^ 16 := by
    rw [masked_post, UScalar.cast_val_eq]; rfl
  have hsize16 : U16.size = 65536 := by simp [U16.size_def, U16.numBits_def]
  by_cases hi6z : i6 = 0#u32
  · simp only [hi6z, ite_true, bind_ok]
    step*
    all_goals
      simp at i7_post
      rw [hsize16] at m1_post m2_post m3_post
      have hr : r.val = i8.val % 2 ^ 16 := by rw [r_post, UScalar.cast_val_eq]; rfl
    all_goals first
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr rfl
           rfl rfl).1)
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr
           i9_post rfl rfl).2.1)
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr
           i9_post i10_post rfl).2.2.1)
      | skip
    obtain ⟨-, -, -, hval⟩ := swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post
      i8_post hr i9_post i10_post chunk2_post
    have hi6v : i6.val = 0 := by rw [hi6z]; simp
    -- the test passed: all digits, and the value is theirs
    rename_i hsum0
    have hsum0' : sum.val = 0 := by rw [of_decide_eq_true hsum0]; simp
    have hd := htest'.mp ⟨hi6v, hsum0'⟩
    refine ⟨hd, ?_⟩
    obtain ⟨d0, d1, d2, d3⟩ := hdig.mp hd
    have hlt := hdigc.mpr hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
    obtain ⟨l0, l1, l2, l3⟩ := hlt
    rw [hval, hdec, byte_and15 c0 (by omega), byte_and15 c1 (by omega), byte_and15 c2 (by omega),
      byte_and15 c3 (by omega), hc0, hc1, hc2, hc3, isDigit_xor_val b0 d0, isDigit_xor_val b1 d1,
      isDigit_xor_val b2 d2, isDigit_xor_val b3 d3]
    ring
  · simp only [hi6z, ite_false, bind_ok]
    step*
    all_goals
      simp at i7_post
      rw [hsize16] at m1_post m2_post m3_post
      have hr : r.val = i8.val % 2 ^ 16 := by rw [r_post, UScalar.cast_val_eq]; rfl
    all_goals first
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr rfl
           rfl rfl).1)
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr
           i9_post rfl rfl).2.1)
      | (rw [U16.max_eq]
         exact (swar4_fold2 he0 he2 hchunk hmasked m1_post m2_post m3_post i7_post i8_post hr
           i9_post i10_post rfl).2.2.1)

end atoi_radix10
