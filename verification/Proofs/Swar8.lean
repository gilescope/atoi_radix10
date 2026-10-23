import Proofs.Fold
import Proofs.Swar4

/-!
`parse_8_chars` (`src/lib.rs`): eight bytes, three folds. With `c_i = b_i ^ 0x30`:

  `lanes 8 [c0 … c7]` → `lanes 16 [10c0+c1, …]` → `lanes 32 [100e0+e1, 100e2+e3]` → `10000f0 + f1`

the first two by `fold_step`, the last by a mask-and-cast.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- Constants of `parse_8_chars`, as lanes. -/
theorem c8_zeros : (3472328296227680304 : ℕ) = lanes 8 (List.replicate 8 48) := by
  norm_num [lanes]
theorem c8_hi : (17361641481138401520 : ℕ) = lanes 8 (List.replicate 8 240) := by norm_num [lanes]
theorem c8_76 : (8536140394893047414 : ℕ) = lanes 8 (List.replicate 8 118) := by norm_num [lanes]
theorem c8_80 : (9259542123273814144 : ℕ) = lanes 8 (List.replicate 8 128) := by norm_num [lanes]
theorem c8_odd1 : (1080880403494997760 : ℕ) = lanes 8 (oddMask 15 4) := by
  norm_num [lanes, oddMask]
theorem c8_even1 : (4222189076152335 : ℕ) = lanes 8 (evenMask 15 4) := by
  norm_num [lanes, evenMask]
theorem c8_odd2 : (71776119077928960 : ℕ) = lanes 16 (oddMask 255 2) := by
  norm_num [lanes, oddMask]
theorem c8_even2 : (1095216660735 : ℕ) = lanes 16 (evenMask 255 2) := by
  norm_num [lanes, evenMask]
theorem c8_odd3 : (281470681743360 : ℕ) = lanes 32 [0, 65535] := by norm_num [lanes]

/-- A folded lane is at most `c·m + m`. -/
theorem pairFold_mem_le (c m : ℕ) :
    ∀ gs : List ℕ, ∀ x ∈ pairFold c (gs.map (· &&& m)), x ≤ c * m + m
  | g0 :: g1 :: rest => by
    simp only [List.map_cons, pairFold, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, pairFold_mem_le c m rest⟩
    have h0 := Nat.and_le_right (n := g0) (m := m)
    have h1 := Nat.and_le_right (n := g1) (m := m)
    nlinarith
  | [] => by simp [pairFold]
  | [_] => by simp [pairFold]

/-- Full-lane masks leave small lanes alone. -/
theorem map_and_mask_eq_self (k : ℕ) (es : List ℕ) (hes : ∀ e ∈ es, e < 2 ^ k) :
    es.map (· &&& (2 ^ k - 1)) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hes e (by simp)),
      ih (fun e he => hes e (by simp [he]))]

theorem pairFold_length (c : ℕ) (gs : List ℕ) (n : ℕ) (h : gs.length = 2 * n) :
    (pairFold c gs).length = n := by
  induction n generalizing gs with
  | zero => cases gs with | nil => rfl | cons => simp at h
  | succ n ih =>
    match gs, h with
    | g0 :: g1 :: rest, h => simp only [pairFold, List.length_cons]; rw [ih rest (by simp at h; omega)]

/-- `x & (2^k - 1) = x` below `2^k`. -/
theorem and_mask_of_lt (x k : ℕ) (h : x < 2 ^ k) : x &&& (2 ^ k - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- The first fold, bytes to pairs of digits. `cs` are the bytes after `^ 0x30`. -/
theorem fold8_1 {cs : List ℕ} {chunk i6 lower i7 upper chunk1 : ℕ}
    (hcs : ∀ c ∈ cs, c < 2 ^ 8) (hlen : cs.length = 8) (hchunk : chunk = lanes 8 cs)
    (hi6 : i6 = chunk &&& 1080880403494997760) (hlower : lower = i6 >>> 8)
    (hi7 : i7 = chunk &&& 4222189076152335) (hupper : upper = i7 * 10)
    (hchunk1 : chunk1 = lower + upper) :
    i7 * 10 ≤ 18446744073709551615 ∧ lower + upper ≤ 18446744073709551615 ∧
      chunk1 = lanes 16 (pairFold 10 (cs.map (· &&& 15))) := by
  have hfold := fold_step 8 15 10 4 (by norm_num) cs (by omega) hcs (by norm_num)
  rw [← c8_odd1, ← c8_even1, ← hchunk, ← hi6, ← hlower, ← hi7, ← hupper, ← hchunk1,
    show (2 * 8 : ℕ) = 16 by norm_num] at hfold
  have hlt : lanes 16 (pairFold 10 (cs.map (· &&& 15))) < (2 ^ 16) ^ 4 := by
    have := lanes_lt 16 (pairFold 10 (cs.map (· &&& 15)))
      (fun x hx => by have := pairFold_mem_le 10 15 cs x hx; omega)
    rwa [pairFold_length 10 _ 4 (by simp [hlen])] at this
  refine ⟨?_, ?_, hfold⟩ <;> omega

/-- The second fold, pairs to quadruples of digits. `es` are the pairs, each below 256. -/
theorem fold8_2 {es : List ℕ} {chunk1 i8 lower i9 upper chunk2 : ℕ}
    (hes : ∀ e ∈ es, e < 2 ^ 8) (hlen : es.length = 4) (hchunk1 : chunk1 = lanes 16 es)
    (hi8 : i8 = chunk1 &&& 71776119077928960) (hlower : lower = i8 >>> 16)
    (hi9 : i9 = chunk1 &&& 1095216660735) (hupper : upper = i9 * 100)
    (hchunk2 : chunk2 = lower + upper) :
    i9 * 100 ≤ 18446744073709551615 ∧ lower + upper ≤ 18446744073709551615 ∧
      chunk2 = lanes 32 (pairFold 100 es) := by
  have hes16 : ∀ e ∈ es, e < 2 ^ 16 := fun e he => by have := hes e he; omega
  have hfold := fold_step 16 255 100 2 (by norm_num) es (by omega) hes16 (by norm_num)
  rw [← c8_odd2, ← c8_even2, ← hchunk1, ← hi8, ← hlower, ← hi9, ← hupper, ← hchunk2,
    show (2 * 16 : ℕ) = 32 by norm_num] at hfold
  have hmap : es.map (· &&& 255) = es := map_and_mask_eq_self 8 es hes
  rw [hmap] at hfold
  have hlt : lanes 32 (pairFold 100 es) < (2 ^ 32) ^ 2 := by
    have hb : ∀ x ∈ pairFold 100 es, x < 2 ^ 32 := by
      have := pairFold_mem_le 100 255 es; rw [hmap] at this
      intro x hx; have := this x hx; omega
    have := lanes_lt 32 (pairFold 100 es) hb
    rwa [pairFold_length 100 _ 2 (by simp [hlen])] at this
  refine ⟨?_, ?_, hfold⟩ <;> omega

/-- The last step, two quadruples to the value: the high lane shifted down, the low lane cast
and scaled. -/
theorem fold8_3 {f0 f1 chunk2 i10 i11 lower i12 upper chunk3 : ℕ}
    (hf0 : f0 < 2 ^ 16) (hf1 : f1 < 2 ^ 16) (hchunk2 : chunk2 = lanes 32 [f0, f1])
    (hi10 : i10 = chunk2 &&& 281470681743360) (hi11 : i11 = i10 >>> 32)
    (hlower : lower = i11 % 2 ^ 32) (hi12 : i12 = chunk2 % 2 ^ 32) (hupper : upper = i12 * 10000)
    (hchunk3 : chunk3 = lower + upper) :
    i12 * 10000 ≤ 4294967295 ∧ lower + upper ≤ 4294967295 ∧ chunk3 = 10000 * f0 + f1 := by
  have hfs : ∀ x ∈ [f0, f1], x < 2 ^ 32 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  have hi10' : i10 = lanes 32 [0, f1] := by
    rw [hi10, hchunk2, c8_odd3, lanes_and 32 [f0, f1] [0, 65535] hfs (by decide) rfl]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, Nat.and_zero]
    rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, and_mask_of_lt f1 16 hf1]
  have hi11' : i11 = f1 := by
    rw [hi11, hi10', Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 32 = (2 ^ 32) ^ 1 by norm_num,
      lanes_div 32 1 [0, f1] (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega)]
    simp
  have hlower' : lower = f1 := by rw [hlower, hi11', Nat.mod_eq_of_lt (by omega)]
  have hi12' : i12 = f0 := by
    rw [hi12, hchunk2, show (2 : ℕ) ^ 32 = (2 ^ 32) ^ 1 by norm_num, lanes_mod 32 1 [f0, f1] hfs]
    simp
  refine ⟨by rw [hi12']; omega, by rw [hlower', hupper, hi12']; omega, ?_⟩
  rw [hchunk3, hlower', hupper, hi12']; ring

end atoi_radix10

namespace atoi_radix10

/-- `x ^ k` lane by lane. -/
theorem zipWith_xor_replicate (bs : List ℕ) (k : ℕ) :
    List.zipWith (· ^^^ ·) bs (List.replicate bs.length k) = bs.map (· ^^^ k) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.replicate_succ, ih]

/-- The whole arithmetic of `parse_8_chars` after `^ 0x30`: every overflow check holds and
the value is the three folds of the digit lanes. Later steps may be left to unification
(`rfl`) when only an earlier bound is wanted. -/
theorem swar8_all {cs : List ℕ}
    {chunk i6 lower i7 upper chunk1 i8 lower1 i9 upper1 chunk2 i10 i11 lower2 i12 upper2 chunk3 :
      ℕ}
    (hcs : ∀ c ∈ cs, c < 2 ^ 8) (hlen : cs.length = 8) (hchunk : chunk = lanes 8 cs)
    (hi6 : i6 = chunk &&& 1080880403494997760) (hlower : lower = i6 >>> 8)
    (hi7 : i7 = chunk &&& 4222189076152335) (hupper : upper = i7 * 10)
    (hchunk1 : chunk1 = lower + upper)
    (hi8 : i8 = chunk1 &&& 71776119077928960) (hlower1 : lower1 = i8 >>> 16)
    (hi9 : i9 = chunk1 &&& 1095216660735) (hupper1 : upper1 = i9 * 100)
    (hchunk2 : chunk2 = lower1 + upper1)
    (hi10 : i10 = chunk2 &&& 281470681743360) (hi11 : i11 = i10 >>> 32)
    (hlower2 : lower2 = i11 % 2 ^ 32) (hi12 : i12 = chunk2 % 2 ^ 32)
    (hupper2 : upper2 = i12 * 10000) (hchunk3 : chunk3 = lower2 + upper2) :
    i7 * 10 ≤ 18446744073709551615 ∧ lower + upper ≤ 18446744073709551615 ∧
      i9 * 100 ≤ 18446744073709551615 ∧ lower1 + upper1 ≤ 18446744073709551615 ∧
      i12 * 10000 ≤ 4294967295 ∧ lower2 + upper2 ≤ 4294967295 ∧
      chunk3 = lanes 64 (pairFold 10000 (pairFold 100 (pairFold 10 (cs.map (· &&& 15))))) := by
  obtain ⟨hb1, hb2, hchunk1'⟩ := fold8_1 hcs hlen hchunk hi6 hlower hi7 hupper hchunk1
  set es := pairFold 10 (cs.map (· &&& 15)) with hes_def
  have hes : ∀ e ∈ es, e < 2 ^ 8 := fun e he => by have := pairFold_mem_le 10 15 cs e he; omega
  have hes_len : es.length = 4 := pairFold_length 10 _ 4 (by simp [hlen])
  obtain ⟨hb3, hb4, hchunk2'⟩ := fold8_2 hes hes_len hchunk1' hi8 hlower1 hi9 hupper1 hchunk2
  obtain ⟨f0, f1, hf⟩ := List.length_eq_two.mp (pairFold_length 100 es 2 (by omega))
  have hfs : ∀ f ∈ pairFold 100 es, f < 2 ^ 16 := fun f hf => by
    have := pairFold_mem_le 100 255 es
    have hm := map_and_mask_eq_self 8 es hes
    rw [show (2 : ℕ) ^ 8 - 1 = 255 by norm_num] at hm
    rw [hm] at this
    have := this f hf; omega
  have hf0 : f0 < 2 ^ 16 := hfs f0 (by simp [hf])
  have hf1 : f1 < 2 ^ 16 := hfs f1 (by simp [hf])
  rw [hf] at hchunk2'
  obtain ⟨hb5, hb6, hval⟩ := fold8_3 hf0 hf1 hchunk2' hi10 hi11 hlower2 hi12 hupper2 hchunk3
  refine ⟨hb1, hb2, hb3, hb4, hb5, hb6, ?_⟩
  rw [hval, hf]; simp [pairFold, lanes]

/-- `parse_8_chars`: on a slice of at least eight bytes, `Ok` of their decimal value exactly
when all eight are ASCII digits, `Err(InvalidDigit)` otherwise. -/
theorem parse_8_chars_spec (s : Slice U8) (h : 8 ≤ s.val.length) :
    parse_8_chars s ⦃ r =>
      match r with
      | .Ok v => (∀ b ∈ s.val.take 8, isDigit b) ∧ v.val = decimal (s.val.take 8)
      | .Err e => ¬ (∀ b ∈ s.val.take 8, isDigit b) ∧ e.kind = .InvalidDigit ⦄ := by
  -- the eight bytes
  obtain ⟨l, hl⟩ : ∃ l, s.val = l := ⟨_, rfl⟩
  rw [hl] at h
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    <;> simp at h
  have hlen : 8 ≤ s.val.length := by rw [hl]; simp
  set bs : List ℕ := [b0.val, b1.val, b2.val, b3.val, b4.val, b5.val, b6.val, b7.val] with hbs_def
  have hbs : ∀ x ∈ bs, x < 2 ^ 8 := by
    intro x hx
    simp only [hbs_def, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> scalar_tac
  set cs : List ℕ := bs.map (· ^^^ 48) with hcs_def
  have hcs : ∀ c ∈ cs, c < 2 ^ 8 := by
    intro c hc
    simp only [hcs_def, List.mem_map] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    exact Nat.xor_lt_two_pow (hbs b hb) (by norm_num)
  have hcs_len : cs.length = 8 := by simp [hcs_def, hbs_def]
  have hle : leBytes (s.val.take 8) = lanes 8 bs := by rw [hl]; simp [leBytes_eq_lanes, hbs_def]
  have hdig : (∀ b ∈ s.val.take 8, isDigit b) ↔ ∀ c ∈ cs, c ≤ 9 := by
    rw [hl]; simp [hcs_def, hbs_def, isDigit_iff_xor]
  have htest := digit_test cs hcs
  rw [hcs_len, ← hdig] at htest
  have hsize64 : U64.size = (2 ^ 8) ^ 8 := by simp [U64.size_def, U64.numBits_def]
  unfold parse_8_chars
  step*
  all_goals
    simp only [parse_8_chars.ASCII_ZEROS] at chunk_post
    simp at chunk_post i6_post i7_post
    rw [hle] at i1_post
    have hchunk : chunk.val = lanes 8 cs := by
      rw [chunk_post, i1_post, c8_zeros,
        lanes_xor 8 bs (List.replicate 8 48) hbs (by decide) (by simp [hbs_def]),
        show (8 : ℕ) = bs.length by simp [hbs_def], zipWith_xor_replicate]
  -- the six overflow checks, in order
  all_goals first
    | (rw [U64.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl rfl rfl).1)
    | (rw [U64.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post upper_digits_post rfl
         rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).2.1)
    | (simp at i8_post i9_post
       rw [U64.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post upper_digits_post
         chunk1_post i8_post lower_digits1_post i9_post rfl rfl rfl rfl rfl rfl rfl rfl).2.2.1)
    | (simp at i8_post i9_post
       rw [U64.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post upper_digits_post
         chunk1_post i8_post lower_digits1_post i9_post upper_digits1_post rfl rfl rfl rfl rfl rfl
         rfl).2.2.2.1)
    | (simp at i8_post i9_post i10_post
       have hlower2 : lower_digits2.val = i11.val % 2 ^ 32 := by
         rw [lower_digits2_post, UScalar.cast_val_eq]; rfl
       have hi12 : i12.val = chunk2.val % 2 ^ 32 := by rw [i12_post, UScalar.cast_val_eq]; rfl
       rw [U32.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post upper_digits_post
         chunk1_post i8_post lower_digits1_post i9_post upper_digits1_post chunk2_post i10_post
         i11_post hlower2 hi12 rfl rfl).2.2.2.2.1)
    | (simp at i8_post i9_post i10_post
       have hlower2 : lower_digits2.val = i11.val % 2 ^ 32 := by
         rw [lower_digits2_post, UScalar.cast_val_eq]; rfl
       have hi12 : i12.val = chunk2.val % 2 ^ 32 := by rw [i12_post, UScalar.cast_val_eq]; rfl
       rw [U32.max_eq]
       exact (swar8_all hcs hcs_len hchunk i6_post lower_digits_post i7_post upper_digits_post
         chunk1_post i8_post lower_digits1_post i9_post upper_digits1_post chunk2_post i10_post
         i11_post hlower2 hi12 upper_digits2_post rfl).2.2.2.2.2.1)
    | skip
  -- the two outcomes
  all_goals
    simp at i2_post i4_post i5_post i8_post i9_post i10_post
    have hlower2 : lower_digits2.val = i11.val % 2 ^ 32 := by
      rw [lower_digits2_post, UScalar.cast_val_eq]; rfl
    have hi12 : i12.val = chunk2.val % 2 ^ 32 := by rw [i12_post, UScalar.cast_val_eq]; rfl
    obtain ⟨-, -, -, -, -, -, hval⟩ := swar8_all hcs hcs_len hchunk i6_post lower_digits_post
      i7_post upper_digits_post chunk1_post i8_post lower_digits1_post i9_post upper_digits1_post
      chunk2_post i10_post i11_post hlower2 hi12 upper_digits2_post chunk3_post
    have hi5 : (i5.val = 0) ↔ (i2.val = 0 ∧ i4.val = 0) := by rw [i5_post, Nat.or_eq_zero_iff]
    have h76 : (8536140394893047414#u64 : U64).val = 8536140394893047414 := by simp
    have hi4 : i4.val = ((lanes 8 cs + lanes 8 (List.replicate 8 118)) % (2 ^ 8) ^ 8) &&&
        lanes 8 (List.replicate 8 128) := by
      rw [i4_post, i3_post, core.num.U64.wrapping_add_val_eq, UScalar.size_UScalarTyU64, hsize64,
        hchunk, h76, c8_76, c8_80]
    have hi2 : i2.val = lanes 8 cs &&& lanes 8 (List.replicate 8 240) := by
      simp only [parse_8_chars.MASK_HI] at i2_post
      simp at i2_post
      rw [i2_post, hchunk, c8_hi]
    rw [← hi2, ← hi4, ← hi5] at htest
  case h1 =>
    have hz : i5.val = 0 := by rw [‹i5 = 0#u64›]; simp
    have hd := htest.mp hz
    refine ⟨hd, ?_⟩
    have hd9 := hdig.mp hd
    have hmap15 : cs.map (· &&& 15) = cs := by
      have := map_and_mask_eq_self 4 cs (fun c hc => by have := hd9 c hc; omega)
      rwa [show (2 : ℕ) ^ 4 - 1 = 15 by norm_num] at this
    rw [hl] at hd
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hd
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := hd
    have hcsval : cs = [b0.val - 48, b1.val - 48, b2.val - 48, b3.val - 48, b4.val - 48,
        b5.val - 48, b6.val - 48, b7.val - 48] := by
      simp only [hcs_def, hbs_def, List.map_cons, List.map_nil]
      rw [isDigit_xor_val b0 d0, isDigit_xor_val b1 d1, isDigit_xor_val b2 d2,
        isDigit_xor_val b3 d3, isDigit_xor_val b4 d4, isDigit_xor_val b5 d5,
        isDigit_xor_val b6 d6, isDigit_xor_val b7 d7]
    rw [hval, hmap15, hcsval, hl]
    simp [pairFold, lanes, decimal]
    ring
  case h2 =>
    intro hd
    apply ‹¬ i5 = 0#u64›
    exact UScalar.eq_of_val_eq (by rw [htest.mpr hd]; simp)

end atoi_radix10
