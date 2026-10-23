import Proofs.Swar8

/-!
`parse_16_chars` (`src/lib.rs`): sixteen bytes, four folds (`fold_step` three times, then the
mask-and-cast step), value in `u64`.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- Constants of `parse_16_chars`, as lanes. -/
theorem c16_zeros : (64053151420411946063694043751862251568 : ℕ) = lanes 8 (List.replicate 16 48) := by
  norm_num [lanes]
theorem c16_hi : (320265757102059730318470218759311257840 : ℕ) = lanes 8 (List.replicate 16 240) := by
  norm_num [lanes]
theorem c16_76 : (157463997241846034073247857556661368438 : ℕ) = lanes 8 (List.replicate 16 118) := by
  norm_num [lanes]
theorem c16_80 : (170808403787765189503184116671632670848 : ℕ) = lanes 8 (List.replicate 16 128) := by
  norm_num [lanes]
theorem c16_odd1 : (19938724177560138852511764592019377920 : ℕ) = lanes 8 (oddMask 15 8) := by
  norm_num [lanes, oddMask]
theorem c16_even1 : (77885641318594292392624080437575695 : ℕ) = lanes 8 (evenMask 15 8) := by
  norm_num [lanes, evenMask]
theorem c16_odd2 : (1324035699234657129348783122579128320 : ℕ) = lanes 16 (oddMask 255 4) := by
  norm_num [lanes, oddMask]
theorem c16_even2 : (20203181445841325826244859658495 : ℕ) = lanes 16 (evenMask 255 4) := by
  norm_num [lanes, evenMask]
theorem c16_odd3 : (5192217630372313364474373467013120 : ℕ) = lanes 32 (oddMask 65535 2) := by
  norm_num [lanes, oddMask]
theorem c16_even3 : (1208907372870555465220095 : ℕ) = lanes 32 (evenMask 65535 2) := by
  norm_num [lanes, evenMask]
theorem c16_odd4 : (79228162495817593519834398720 : ℕ) = lanes 64 [0, 4294967295] := by
  norm_num [lanes]

/-- Bytes to pairs. -/
theorem fold16_1 {cs : List ℕ} {chunk i2 lower i3 upper chunk1 : ℕ}
    (hcs : ∀ c ∈ cs, c < 2 ^ 8) (hlen : cs.length = 16) (hchunk : chunk = lanes 8 cs)
    (hi2 : i2 = chunk &&& 19938724177560138852511764592019377920) (hlower : lower = i2 >>> 8)
    (hi3 : i3 = chunk &&& 77885641318594292392624080437575695) (hupper : upper = i3 * 10)
    (hchunk1 : chunk1 = lower + upper) :
    i3 * 10 ≤ 340282366920938463463374607431768211455 ∧
      lower + upper ≤ 340282366920938463463374607431768211455 ∧
      chunk1 = lanes 16 (pairFold 10 (cs.map (· &&& 15))) := by
  have hfold := fold_step 8 15 10 8 (by norm_num) cs (by omega) hcs (by norm_num)
  rw [← c16_odd1, ← c16_even1, ← hchunk, ← hi2, ← hlower, ← hi3, ← hupper, ← hchunk1,
    show (2 * 8 : ℕ) = 16 by norm_num] at hfold
  have hlt : lanes 16 (pairFold 10 (cs.map (· &&& 15))) < (2 ^ 16) ^ 8 := by
    have := lanes_lt 16 (pairFold 10 (cs.map (· &&& 15)))
      (fun x hx => by have := pairFold_mem_le 10 15 cs x hx; omega)
    rwa [pairFold_length 10 _ 8 (by simp [hlen])] at this
  refine ⟨?_, ?_, hfold⟩ <;> omega

/-- Pairs to quadruples. -/
theorem fold16_2 {es : List ℕ} {chunk1 i4 lower i5 upper chunk2 : ℕ}
    (hes : ∀ e ∈ es, e < 2 ^ 8) (hlen : es.length = 8) (hchunk1 : chunk1 = lanes 16 es)
    (hi4 : i4 = chunk1 &&& 1324035699234657129348783122579128320) (hlower : lower = i4 >>> 16)
    (hi5 : i5 = chunk1 &&& 20203181445841325826244859658495) (hupper : upper = i5 * 100)
    (hchunk2 : chunk2 = lower + upper) :
    i5 * 100 ≤ 340282366920938463463374607431768211455 ∧
      lower + upper ≤ 340282366920938463463374607431768211455 ∧
      chunk2 = lanes 32 (pairFold 100 es) := by
  have hes16 : ∀ e ∈ es, e < 2 ^ 16 := fun e he => by have := hes e he; omega
  have hfold := fold_step 16 255 100 4 (by norm_num) es (by omega) hes16 (by norm_num)
  rw [← c16_odd2, ← c16_even2, ← hchunk1, ← hi4, ← hlower, ← hi5, ← hupper, ← hchunk2,
    show (2 * 16 : ℕ) = 32 by norm_num] at hfold
  have hmap : es.map (· &&& 255) = es := map_and_mask_eq_self 8 es hes
  rw [hmap] at hfold
  have hlt : lanes 32 (pairFold 100 es) < (2 ^ 32) ^ 4 := by
    have hb : ∀ x ∈ pairFold 100 es, x < 2 ^ 32 := by
      have := pairFold_mem_le 100 255 es; rw [hmap] at this
      intro x hx; have := this x hx; omega
    have := lanes_lt 32 (pairFold 100 es) hb
    rwa [pairFold_length 100 _ 4 (by simp [hlen])] at this
  refine ⟨?_, ?_, hfold⟩ <;> omega

/-- Quadruples to octets. -/
theorem fold16_3 {fs : List ℕ} {chunk2 i6 lower i7 upper chunk3 : ℕ}
    (hfs : ∀ f ∈ fs, f < 2 ^ 16) (hlen : fs.length = 4) (hchunk2 : chunk2 = lanes 32 fs)
    (hi6 : i6 = chunk2 &&& 5192217630372313364474373467013120) (hlower : lower = i6 >>> 32)
    (hi7 : i7 = chunk2 &&& 1208907372870555465220095) (hupper : upper = i7 * 10000)
    (hchunk3 : chunk3 = lower + upper) :
    i7 * 10000 ≤ 340282366920938463463374607431768211455 ∧
      lower + upper ≤ 340282366920938463463374607431768211455 ∧
      chunk3 = lanes 64 (pairFold 10000 fs) := by
  have hfs32 : ∀ f ∈ fs, f < 2 ^ 32 := fun f hf => by have := hfs f hf; omega
  have hfold := fold_step 32 65535 10000 2 (by norm_num) fs (by omega) hfs32 (by norm_num)
  rw [← c16_odd3, ← c16_even3, ← hchunk2, ← hi6, ← hlower, ← hi7, ← hupper, ← hchunk3,
    show (2 * 32 : ℕ) = 64 by norm_num] at hfold
  have hmap : fs.map (· &&& 65535) = fs := map_and_mask_eq_self 16 fs hfs
  rw [hmap] at hfold
  have hlt : lanes 64 (pairFold 10000 fs) < (2 ^ 64) ^ 2 := by
    have hb : ∀ x ∈ pairFold 10000 fs, x < 2 ^ 64 := by
      have := pairFold_mem_le 10000 65535 fs; rw [hmap] at this
      intro x hx; have := this x hx; omega
    have := lanes_lt 64 (pairFold 10000 fs) hb
    rwa [pairFold_length 10000 _ 2 (by simp [hlen])] at this
  refine ⟨?_, ?_, hfold⟩ <;> omega

/-- Two octets to the value. -/
theorem fold16_4 {g0 g1 chunk3 i8 i9 lower i10 upper chunk4 : ℕ}
    (hg0 : g0 < 2 ^ 32) (hg1 : g1 < 2 ^ 32) (hchunk3 : chunk3 = lanes 64 [g0, g1])
    (hi8 : i8 = chunk3 &&& 79228162495817593519834398720) (hi9 : i9 = i8 >>> 64)
    (hlower : lower = i9 % 2 ^ 64) (hi10 : i10 = chunk3 % 2 ^ 64)
    (hupper : upper = i10 * 100000000) (hchunk4 : chunk4 = lower + upper) :
    i10 * 100000000 ≤ 18446744073709551615 ∧ lower + upper ≤ 18446744073709551615 ∧
      chunk4 = 100000000 * g0 + g1 := by
  have hgs : ∀ x ∈ [g0, g1], x < 2 ^ 64 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  have hi8' : i8 = lanes 64 [0, g1] := by
    rw [hi8, hchunk3, c16_odd4, lanes_and 64 [g0, g1] [0, 4294967295] hgs (by decide) rfl]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, Nat.and_zero]
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, and_mask_of_lt g1 32 hg1]
  have hi9' : i9 = g1 := by
    rw [hi9, hi8', Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 64 = (2 ^ 64) ^ 1 by norm_num,
      lanes_div 64 1 [0, g1] (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega)]
    simp
  have hlower' : lower = g1 := by rw [hlower, hi9', Nat.mod_eq_of_lt (by omega)]
  have hi10' : i10 = g0 := by
    rw [hi10, hchunk3, show (2 : ℕ) ^ 64 = (2 ^ 64) ^ 1 by norm_num, lanes_mod 64 1 [g0, g1] hgs]
    simp
  refine ⟨by rw [hi10']; omega, by rw [hlower', hupper, hi10']; omega, ?_⟩
  rw [hchunk4, hlower', hupper, hi10']; ring

/-- The whole arithmetic of `parse_16_chars` after `^ 0x30`. -/
theorem swar16_all {cs : List ℕ}
    {chunk i2 lower i3 upper chunk1 i4 lower1 i5 upper1 chunk2 i6 lower2 i7 upper2 chunk3 i8 i9
      lower3 i10 upper3 chunk4 : ℕ}
    (hcs : ∀ c ∈ cs, c < 2 ^ 8) (hlen : cs.length = 16) (hchunk : chunk = lanes 8 cs)
    (hi2 : i2 = chunk &&& 19938724177560138852511764592019377920) (hlower : lower = i2 >>> 8)
    (hi3 : i3 = chunk &&& 77885641318594292392624080437575695) (hupper : upper = i3 * 10)
    (hchunk1 : chunk1 = lower + upper)
    (hi4 : i4 = chunk1 &&& 1324035699234657129348783122579128320) (hlower1 : lower1 = i4 >>> 16)
    (hi5 : i5 = chunk1 &&& 20203181445841325826244859658495) (hupper1 : upper1 = i5 * 100)
    (hchunk2 : chunk2 = lower1 + upper1)
    (hi6 : i6 = chunk2 &&& 5192217630372313364474373467013120) (hlower2 : lower2 = i6 >>> 32)
    (hi7 : i7 = chunk2 &&& 1208907372870555465220095) (hupper2 : upper2 = i7 * 10000)
    (hchunk3 : chunk3 = lower2 + upper2)
    (hi8 : i8 = chunk3 &&& 79228162495817593519834398720) (hi9 : i9 = i8 >>> 64)
    (hlower3 : lower3 = i9 % 2 ^ 64) (hi10 : i10 = chunk3 % 2 ^ 64)
    (hupper3 : upper3 = i10 * 100000000) (hchunk4 : chunk4 = lower3 + upper3) :
    i3 * 10 ≤ 340282366920938463463374607431768211455 ∧
      lower + upper ≤ 340282366920938463463374607431768211455 ∧
      i5 * 100 ≤ 340282366920938463463374607431768211455 ∧
      lower1 + upper1 ≤ 340282366920938463463374607431768211455 ∧
      i7 * 10000 ≤ 340282366920938463463374607431768211455 ∧
      lower2 + upper2 ≤ 340282366920938463463374607431768211455 ∧
      i10 * 100000000 ≤ 18446744073709551615 ∧ lower3 + upper3 ≤ 18446744073709551615 ∧
      chunk4 = lanes 128 (pairFold 100000000 (pairFold 10000 (pairFold 100
        (pairFold 10 (cs.map (· &&& 15)))))) := by
  obtain ⟨hb1, hb2, hchunk1'⟩ := fold16_1 hcs hlen hchunk hi2 hlower hi3 hupper hchunk1
  set es := pairFold 10 (cs.map (· &&& 15)) with hes_def
  have hes : ∀ e ∈ es, e < 2 ^ 8 := fun e he => by have := pairFold_mem_le 10 15 cs e he; omega
  have hes_len : es.length = 8 := pairFold_length 10 _ 8 (by simp [hlen])
  obtain ⟨hb3, hb4, hchunk2'⟩ := fold16_2 hes hes_len hchunk1' hi4 hlower1 hi5 hupper1 hchunk2
  set fs := pairFold 100 es with hfs_def
  have hfs : ∀ f ∈ fs, f < 2 ^ 16 := fun f hf => by
    have := pairFold_mem_le 100 255 es
    have hm := map_and_mask_eq_self 8 es hes
    rw [show (2 : ℕ) ^ 8 - 1 = 255 by norm_num] at hm
    rw [hm] at this
    have := this f hf; omega
  have hfs_len : fs.length = 4 := pairFold_length 100 _ 4 (by omega)
  obtain ⟨hb5, hb6, hchunk3'⟩ := fold16_3 hfs hfs_len hchunk2' hi6 hlower2 hi7 hupper2 hchunk3
  obtain ⟨g0, g1, hg⟩ := List.length_eq_two.mp (pairFold_length 10000 fs 2 (by omega))
  have hgs : ∀ g ∈ pairFold 10000 fs, g < 2 ^ 32 := fun g hg => by
    have := pairFold_mem_le 10000 65535 fs
    have hm := map_and_mask_eq_self 16 fs hfs
    rw [show (2 : ℕ) ^ 16 - 1 = 65535 by norm_num] at hm
    rw [hm] at this
    have := this g hg; omega
  have hg0 : g0 < 2 ^ 32 := hgs g0 (by simp [hg])
  have hg1 : g1 < 2 ^ 32 := hgs g1 (by simp [hg])
  rw [hg] at hchunk3'
  obtain ⟨hb7, hb8, hval⟩ := fold16_4 hg0 hg1 hchunk3' hi8 hi9 hlower3 hi10 hupper3 hchunk4
  refine ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, ?_⟩
  rw [hval, hg]; simp [pairFold, lanes]

end atoi_radix10

namespace atoi_radix10

/-- `parse_16_chars`: on a slice of at least sixteen bytes, `Ok` of their decimal value exactly
when all sixteen are ASCII digits, `Err(InvalidDigit)` otherwise. -/
theorem parse_16_chars_spec (s : Slice U8) (h : 16 ≤ s.val.length) :
    parse_16_chars s ⦃ r =>
      match r with
      | .Ok v => (∀ b ∈ s.val.take 16, isDigit b) ∧ v.val = decimal (s.val.take 16)
      | .Err e => ¬ (∀ b ∈ s.val.take 16, isDigit b) ∧ e.kind = .InvalidDigit ⦄ := by
  -- the sixteen bytes
  obtain ⟨l, hl⟩ : ∃ l, s.val = l := ⟨_, rfl⟩
  rw [hl] at h
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8,
    _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    <;> simp at h
  have hlen : 16 ≤ s.val.length := by rw [hl]; simp
  set bs : List ℕ := [b0.val, b1.val, b2.val, b3.val, b4.val, b5.val, b6.val, b7.val, b8.val,
    b9.val, b10.val, b11.val, b12.val, b13.val, b14.val, b15.val] with hbs_def
  have hbs : ∀ x ∈ bs, x < 2 ^ 8 := by
    intro x hx
    simp only [hbs_def, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;> scalar_tac
  set cs : List ℕ := bs.map (· ^^^ 48) with hcs_def
  have hcs : ∀ c ∈ cs, c < 2 ^ 8 := by
    intro c hc
    simp only [hcs_def, List.mem_map] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    exact Nat.xor_lt_two_pow (hbs b hb) (by norm_num)
  have hcs_len : cs.length = 16 := by simp [hcs_def, hbs_def]
  have hle : leBytes (s.val.take 16) = lanes 8 bs := by rw [hl]; simp [leBytes_eq_lanes, hbs_def]
  have hdig : (∀ b ∈ s.val.take 16, isDigit b) ↔ ∀ c ∈ cs, c ≤ 9 := by
    rw [hl]; simp [hcs_def, hbs_def, isDigit_iff_xor]
  have htest := digit_test cs hcs
  rw [hcs_len, ← hdig] at htest
  have hsize128 : U128.size = (2 ^ 8) ^ 16 := by simp [U128.size_def, U128.numBits_def]
  unfold parse_16_chars
  step*
  all_goals
    simp only [parse_16_chars.ASCII_ZEROS] at chunk_post
    simp at chunk_post i2_post i3_post
    rw [hle] at i1_post
    have hchunk : chunk.val = lanes 8 cs := by
      rw [chunk_post, i1_post, c16_zeros,
        lanes_xor 8 bs (List.replicate 16 48) hbs (by decide) (by simp [hbs_def]),
        show (16 : ℕ) = bs.length by simp [hbs_def], zipWith_xor_replicate]
  -- the eight overflow checks, in order
  all_goals first
    | (rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).1)
    | (rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).2.1)
    | (simp at i4_post i5_post
       rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
         rfl rfl rfl).2.2.1)
    | (simp at i4_post i5_post
       rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post upper_digits1_post rfl rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl).2.2.2.1)
    | (simp at i4_post i5_post i6_post i7_post
       rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post upper_digits1_post chunk2_post i6_post
         lower_digits2_post i7_post rfl rfl rfl rfl rfl rfl rfl rfl).2.2.2.2.1)
    | (simp at i4_post i5_post i6_post i7_post
       rw [U128.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post upper_digits1_post chunk2_post i6_post
         lower_digits2_post i7_post upper_digits2_post rfl rfl rfl rfl rfl rfl rfl).2.2.2.2.2.1)
    | (simp at i4_post i5_post i6_post i7_post i8_post
       have hlower3 : lower_digits3.val = i9.val % 2 ^ 64 := by
         rw [lower_digits3_post, UScalar.cast_val_eq]; rfl
       have hi10 : i10.val = chunk3.val % 2 ^ 64 := by rw [i10_post, UScalar.cast_val_eq]; rfl
       rw [U64.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post upper_digits1_post chunk2_post i6_post
         lower_digits2_post i7_post upper_digits2_post chunk3_post i8_post i9_post hlower3 hi10
         rfl rfl).2.2.2.2.2.2.1)
    | (simp at i4_post i5_post i6_post i7_post i8_post
       have hlower3 : lower_digits3.val = i9.val % 2 ^ 64 := by
         rw [lower_digits3_post, UScalar.cast_val_eq]; rfl
       have hi10 : i10.val = chunk3.val % 2 ^ 64 := by rw [i10_post, UScalar.cast_val_eq]; rfl
       rw [U64.max_eq]
       exact (swar16_all hcs hcs_len hchunk i2_post lower_digits_post i3_post upper_digits_post
         chunk1_post i4_post lower_digits1_post i5_post upper_digits1_post chunk2_post i6_post
         lower_digits2_post i7_post upper_digits2_post chunk3_post i8_post i9_post hlower3 hi10
         upper_digits3_post rfl).2.2.2.2.2.2.2.1)
    | skip
  -- the two outcomes
  all_goals
    simp at i4_post i5_post i6_post i7_post i8_post i11_post i12_post i13_post
    have hlower3 : lower_digits3.val = i9.val % 2 ^ 64 := by
      rw [lower_digits3_post, UScalar.cast_val_eq]; rfl
    have hi10 : i10.val = chunk3.val % 2 ^ 64 := by rw [i10_post, UScalar.cast_val_eq]; rfl
    obtain ⟨-, -, -, -, -, -, -, -, hval⟩ := swar16_all hcs hcs_len hchunk i2_post
      lower_digits_post i3_post upper_digits_post chunk1_post i4_post lower_digits1_post i5_post
      upper_digits1_post chunk2_post i6_post lower_digits2_post i7_post upper_digits2_post
      chunk3_post i8_post i9_post hlower3 hi10 upper_digits3_post chunk4_post
    have hi13 : (i13.val = 0) ↔ (i11.val = 0 ∧ i12.val = 0) := by
      rw [i13_post, Nat.or_eq_zero_iff]
    have h76 : (157463997241846034073247857556661368438#u128 : U128).val =
        157463997241846034073247857556661368438 := by simp
    have hi12 : i12.val = ((lanes 8 cs + lanes 8 (List.replicate 16 118)) % (2 ^ 8) ^ 16) &&&
        lanes 8 (List.replicate 16 128) := by
      rw [i12_post, chk_post, core.num.U128.wrapping_add_val_eq, UScalar.size_UScalarTyU128,
        hsize128, hchunk, h76, c16_76, c16_80]
    have hi11 : i11.val = lanes 8 cs &&& lanes 8 (List.replicate 16 240) := by
      simp only [parse_16_chars.MASK_HI] at i11_post
      simp at i11_post
      rw [i11_post, hchunk, c16_hi]
    rw [← hi11, ← hi12, ← hi13] at htest
  case h1 =>
    have hz : i13.val = 0 := by rw [‹i13 = 0#u128›]; simp
    have hd := htest.mp hz
    refine ⟨hd, ?_⟩
    have hd9 := hdig.mp hd
    have hmap15 : cs.map (· &&& 15) = cs := by
      have := map_and_mask_eq_self 4 cs (fun c hc => by have := hd9 c hc; omega)
      rwa [show (2 : ℕ) ^ 4 - 1 = 15 by norm_num] at this
    rw [hl] at hd
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hd
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ := hd
    have hcsval : cs = [b0.val - 48, b1.val - 48, b2.val - 48, b3.val - 48, b4.val - 48,
        b5.val - 48, b6.val - 48, b7.val - 48, b8.val - 48, b9.val - 48, b10.val - 48,
        b11.val - 48, b12.val - 48, b13.val - 48, b14.val - 48, b15.val - 48] := by
      simp only [hcs_def, hbs_def, List.map_cons, List.map_nil]
      rw [isDigit_xor_val b0 d0, isDigit_xor_val b1 d1, isDigit_xor_val b2 d2,
        isDigit_xor_val b3 d3, isDigit_xor_val b4 d4, isDigit_xor_val b5 d5,
        isDigit_xor_val b6 d6, isDigit_xor_val b7 d7, isDigit_xor_val b8 d8,
        isDigit_xor_val b9 d9, isDigit_xor_val b10 d10, isDigit_xor_val b11 d11,
        isDigit_xor_val b12 d12, isDigit_xor_val b13 d13, isDigit_xor_val b14 d14,
        isDigit_xor_val b15 d15]
    rw [hval, hmap15, hcsval, hl]
    simp [pairFold, lanes, decimal]
    ring
  case h2 =>
    intro hd
    apply ‹¬ i13 = 0#u128›
    exact UScalar.eq_of_val_eq (by rw [htest.mpr hd]; simp)

end atoi_radix10
