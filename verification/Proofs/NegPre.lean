import Proofs.NegLoop

/-!
The negative pre-pass (`src/parse.rs` lines 369-526, `parse_inner_loop0_loop0`): the `loop` around the
negative SWAR block. Shorter than `CHARS` digits and not empty: the block, whose 22 result slots
are cascaded into the pre-pass's 25; empty: `Err(Empty)`; exactly `CHARS` long with a small
first digit: that digit set aside with its weight; leading zeros stripped; anything else a
negative overflow.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The pre-pass's exit payload: the state, 25 result slots, and the slices that ride along. -/
abbrev NegPreExit (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T ×
  U8 × Slice U8 × Slice U8 × Slice U8
/-- Its `cont` payload. -/
abbrev NegPreCont (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 × U8 × Slice U8 ×
  Slice U8 × Slice U8

/-- The slots of a pre-pass exit are right. -/
def NegPreSlots {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) : NegPreExit T → Prop
  | (_, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, _, _, _, _) => SlotsOK (NegResult toInt lo hi D0) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25]

/-- The post-condition of a join inside the pre-pass body. -/
def NegPrePost {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) (contOK : NegPreCont T → Prop)
    (inrOK : Prop) : Sum (Sum (NegPreCont T) (NegPreExit T)) Unit → Prop
  | .inl (.inl c) => contOK c
  | .inl (.inr e) => NegPreSlots toInt lo hi D0 e
  | .inr _ => inrOK

/-- What the negative pre-pass maintains: some `a ≤ 0` (the digit set aside, negated) accounts
for the bytes consumed, no proper prefix of the rest can overflow downwards, `checked` holds that
digit with its weight, and the slice is empty exactly when the whole input after the `-` was. -/
structure NegPreInv {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 : List U8) (s : Slice U8)
    (checked : Option (U8 × T)) : Prop where
  acc : ∃ a : ℤ, a ≤ 0 ∧ lo ≤ a ∧ stdDigits lo hi true 0 D0 = stdDigits lo hi true a s.val ∧
    (∀ k, k < s.val.length → k + 1 < c → lo ≤ a * 10 ^ k - (10 ^ k - 1)) ∧
    (checked = none → a = 0) ∧
    (∀ d t, checked = some (d, t) →
      a = -(d.val : ℤ) ∧ toInt t = (d.val : ℤ) * 10 ^ s.val.length ∧ s.val.length + 1 = c)
  empty_iff : s.val = [] ↔ D0 = []

theorem NegHandover.of_pre {T : Type} {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} {D0 : List U8}
    {s : Slice U8} {checked : Option (U8 × T)} (h : NegPreInv toInt lo hi c D0 s checked)
    (hpos : 0 < s.val.length) (hlt : s.val.length < c) : NegHandover toInt lo hi c D0 s.val checked := by
  obtain ⟨⟨a, ha0, halo, hfold, hb, hn, hs⟩, hiff⟩ := h
  refine ⟨hpos, hlt, ⟨a, ha0, halo, hfold, fun k hk => hb k hk (by omega), hn, hs⟩, ?_⟩
  intro h0
  have := hiff.mpr h0
  rw [this] at hpos; simp at hpos

/-- The pre-pass's overflow verdict is right: a first digit with too many digits behind it, or
one too big for a slice of exactly `CHARS` digits, cannot fold into range; a non-digit first is
core's `InvalidDigit`. -/
theorem neg_pre_overflow {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (hlo : lo < 0) (D0 : List U8) (s : Slice U8)
    (d : U8) (hcons : (↑s : List U8) = d :: (↑s : List U8).tail) (hne : D0 ≠ [])
    (hfold : stdDigits lo hi true 0 D0 = stdDigits lo hi true 0 s.val)
    (hcase : (isDigit d ∧ 1 ≤ (d.val : ℤ) - 48 ∧
        (c ≤ s.val.length - 1 ∨ (s.val.length = c ∧ (hi + 1) / 10 ^ (c - 1) < (d.val : ℤ) - 48))) ∨
      ¬ isDigit d) :
    NegResult toInt lo hi D0 (.Err { kind := .NegOverflow }) := by
  have hc3 := hF.three_le_c
  have hsigned := hF.signed hlo
  have hhi9 : (9 : ℤ) ≤ hi := by
    have := hF.hi_ge
    have : (10 : ℤ) ^ 1 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  rcases hcase with ⟨hdd, hd1, hbig⟩ | hnd
  · have hd9 := digit_sub48_le9 hdd
    have hstep : stdDigits lo hi true 0 s.val =
        stdDigits lo hi true (-((d.val : ℤ) - 48)) (↑s : List U8).tail := by
      rw [hcons, stdDigits_neg_cons_digit lo hi 0 d _ hdd ⟨by omega, by omega⟩]; simp
    have htail : (↑s : List U8).tail.length = s.val.length - 1 := by simp
    have hne' : (↑s : List U8).tail ≠ [] := by
      intro h; rw [h] at htail; simp at htail
      rcases hbig with h1 | ⟨h1, _⟩ <;> omega
    obtain ⟨k, hk⟩ : ∃ k, stdDigits lo hi true (-((d.val : ℤ) - 48)) (↑s : List U8).tail = .error k := by
      apply stdDigits_neg_err_of_big lo hi _ _ (by omega) _ hne'
      rw [htail]
      have hp : (0 : ℤ) ≤ 10 ^ (s.val.length - 1) := by positivity
      rcases hbig with h1 | ⟨h1, h2⟩
      · have hlt := hF.hi_lt
        have h10 : (10 : ℤ) ^ c ≤ 10 ^ (s.val.length - 1) := pow_le_pow_right₀ (by norm_num) h1
        nlinarith
      · rw [h1]
        have hfl := fs_floor hi c
        have hp' : (0 : ℤ) ≤ 10 ^ (c - 1) := by positivity
        nlinarith
    refine ⟨k, by rw [negRef_of_ne lo hi hne, hfold, hstep, hk], ?_⟩
    rcases stdDigits_neg_err_kinds lo hi _ _ k hk with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · refine ⟨.InvalidDigit, ?_, Or.inr rfl⟩
    rw [negRef_of_ne lo hi hne, hfold, hcons, stdDigits_nonDigit lo hi true 0 d _ hnd]

set_option maxHeartbeats 4000000 in
theorem parse_inner_loop0_loop0_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (hlo : lo < 0) (D0 : List U8) (t : T)
    (ht : toInt t = lo) (s0 : Slice U8) (is_signed_ty : Bool) (checked : Option (U8 × T))
    (val val1 : U8) (i : U8) (s1 s2 s3 : Slice U8) (h : NegPreInv toInt lo hi c D0 s0 checked) :
    parse.parse_inner_loop0_loop0 inst t s0 is_signed_ty checked val val1 i s1 s2 s3
      ⦃ (out : NegPreExit T) => NegPreSlots toInt lo hi D0 out ⦄ := by
  unfold parse.parse_inner_loop0_loop0
  apply loop.spec_decr_nat (fun p : NegPreCont T => p.1.val.length)
    (fun p : NegPreCont T => match p with
      | (s, b, ch, v, v1, i', t1, t2, t3) => NegPreInv toInt lo hi c D0 s ch)
  · rintro ⟨s, b, ch, v, v1, i', t1, t2, t3⟩ hinv
    have hinv0 := hinv
    obtain ⟨⟨a, ha0, halo, hfold, hbnd, hnone, hsome⟩, hiff⟩ := hinv
    have hc3 := hF.three_le_c
    have hlo' := hF.lo_le
    have hsigned := hF.signed hlo
    have hhi9 : (9 : ℤ) ≤ hi := by
      have := hF.hi_ge
      have : (10 : ℤ) ^ 1 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hC := hF.CHARS
    have hFS := hF.FIRST_SIG
    have hTR := hF.TREE
    have hF8 := hF.from_u8
    have hMul := hF.mul
    unfold parse.parse_inner_loop0_loop0.body
    step as ⟨i1, hi1⟩
    refine WP.spec_bind (Pₘ := NegPrePost toInt lo hi D0 (fun _ => False)
      (c ≤ s.val.length ∨ s.val.length = 0)) ?_ ?_
    · refine WP.spec_ite (fun hlt => ?_) (fun hge => ?_)
      · refine WP.spec_ite (fun hne0 => ?_) (fun heq0 => ?_)
        · -- the block
          have hlen_pos : 0 < s.val.length := by
            have := bne_iff_ne.mp hne0
            have hv : s.len.val ≠ 0 := fun h => this (UScalar.eq_of_val_eq (by rw [h]; simp))
            have hne' : (↑s : List U8) ≠ [] := by
              intro h'; apply hv; rw [Slice.len_val]; simp [Slice.length, h']
            exact List.length_pos_of_ne_nil hne'
          have hlen_lt : s.val.length < c := by
            have := (UScalar.lt_equiv s.len i1).mp hlt
            rw [Slice.len_val] at this; simp [Slice.length] at this; omega
          have hH := NegHandover.of_pre hinv0 hlen_pos hlen_lt
          step as ⟨res, hres⟩
          have hres0 : toInt res = 0 := by have := hres (by simp; omega); simpa using this
          step with parse_inner_loop0_loop0_loop0_spec hF hlo D0 t ht s b ch v v1 s.len res i' t1 t2 t3 s hH hres0
            (Slice.len_val s) as ⟨s5, b', ch', v2, v3, l', res', o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, i2, s6, s7, s8, s9', hpost⟩
          rcases o1 with _ | r1
          · rcases o2 with _ | r2
            · rcases o3 with _ | r3
              · rcases o4 with _ | r4
                · rcases o5 with _ | r5
                  · rcases o6 with _ | r6
                    · rcases o7 with _ | r7
                      · rcases o8 with _ | r8
                        · rcases o9 with _ | r9
                          · rcases o10 with _ | r10
                            · rcases o11 with _ | r11
                              · rcases o12 with _ | r12
                                · rcases o13 with _ | r13
                                  · rcases o14 with _ | r14
                                    · rcases o15 with _ | r15
                                      · rcases o16 with _ | r16
                                        · rcases o17 with _ | r17
                                          · rcases o18 with _ | r18
                                            · rcases o19 with _ | r19
                                              · rcases o20 with _ | r20
                                                · rcases o21 with _ | r21
                                                  · rcases o22 with _ | r22
                                                    · exfalso
                                                      obtain ⟨⟨r, hr⟩, _⟩ := hpost
                                                      simp at hr
                                                    · refine (WP.spec_ok _).mpr ?_
                                                      exact SlotsOK_of_mem (by simp) (hpost.2 r22 (by simp)) (by simp)
                                                  · refine (WP.spec_ok _).mpr ?_
                                                    exact SlotsOK_of_mem (by simp) (hpost.2 r21 (by simp)) (by simp)
                                                · refine (WP.spec_ok _).mpr ?_
                                                  exact SlotsOK_of_mem (by simp) (hpost.2 r20 (by simp)) (by simp)
                                              · refine (WP.spec_ok _).mpr ?_
                                                exact SlotsOK_of_mem (by simp) (hpost.2 r19 (by simp)) (by simp)
                                            · refine (WP.spec_ok _).mpr ?_
                                              exact SlotsOK_of_mem (by simp) (hpost.2 r18 (by simp)) (by simp)
                                          · refine (WP.spec_ok _).mpr ?_
                                            exact SlotsOK_of_mem (by simp) (hpost.2 r17 (by simp)) (by simp)
                                        · refine (WP.spec_ok _).mpr ?_
                                          exact SlotsOK_of_mem (by simp) (hpost.2 r16 (by simp)) (by simp)
                                      · refine (WP.spec_ok _).mpr ?_
                                        exact SlotsOK_of_mem (by simp) (hpost.2 r15 (by simp)) (by simp)
                                    · refine (WP.spec_ok _).mpr ?_
                                      exact SlotsOK_of_mem (by simp) (hpost.2 r14 (by simp)) (by simp)
                                  · refine (WP.spec_ok _).mpr ?_
                                    exact SlotsOK_of_mem (by simp) (hpost.2 r13 (by simp)) (by simp)
                                · refine (WP.spec_ok _).mpr ?_
                                  exact SlotsOK_of_mem (by simp) (hpost.2 r12 (by simp)) (by simp)
                              · refine (WP.spec_ok _).mpr ?_
                                exact SlotsOK_of_mem (by simp) (hpost.2 r11 (by simp)) (by simp)
                            · refine (WP.spec_ok _).mpr ?_
                              exact SlotsOK_of_mem (by simp) (hpost.2 r10 (by simp)) (by simp)
                          · refine (WP.spec_ok _).mpr ?_
                            exact SlotsOK_of_mem (by simp) (hpost.2 r9 (by simp)) (by simp)
                        · refine (WP.spec_ok _).mpr ?_
                          exact SlotsOK_of_mem (by simp) (hpost.2 r8 (by simp)) (by simp)
                      · refine (WP.spec_ok _).mpr ?_
                        exact SlotsOK_of_mem (by simp) (hpost.2 r7 (by simp)) (by simp)
                    · refine (WP.spec_ok _).mpr ?_
                      exact SlotsOK_of_mem (by simp) (hpost.2 r6 (by simp)) (by simp)
                  · refine (WP.spec_ok _).mpr ?_
                    exact SlotsOK_of_mem (by simp) (hpost.2 r5 (by simp)) (by simp)
                · refine (WP.spec_ok _).mpr ?_
                  exact SlotsOK_of_mem (by simp) (hpost.2 r4 (by simp)) (by simp)
              · refine (WP.spec_ok _).mpr ?_
                exact SlotsOK_of_mem (by simp) (hpost.2 r3 (by simp)) (by simp)
            · refine (WP.spec_ok _).mpr ?_
              exact SlotsOK_of_mem (by simp) (hpost.2 r2 (by simp)) (by simp)
          · refine (WP.spec_ok _).mpr ?_
            exact SlotsOK_of_mem (by simp) (hpost.2 r1 (by simp)) (by simp)
        · refine (WP.spec_ok _).mpr ?_
          right
          have := not_not.mp (mt bne_iff_ne.mpr heq0)
          have := congrArg UScalar.val this
          rw [Slice.len_val] at this; simp [Slice.length] at this; simp [this]
      · refine (WP.spec_ok _).mpr ?_
        left
        have := mt (UScalar.lt_equiv s.len i1).mpr hge
        rw [Slice.len_val] at this; simp [Slice.length] at this; omega
    · rintro s4 hs4
      rcases s4 with (c' | e) | u
      · exact (hs4 : False).elim
      · rcases e with ⟨a1, a2, a3, a4, a5, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, a6, a7, a8, a9⟩
        exact (WP.spec_ok _).mpr hs4
      · have hdisj : c ≤ s.val.length ∨ s.val.length = 0 := hs4
        dsimp only
        step as ⟨o, ho⟩
        rcases o with _ | val2
        · -- nothing after the sign: `Err(Empty)`, where core says bad digit
          have hs_nil : (↑s : List U8) = [] := List.head?_eq_none_iff.mp ho.symm
          have hD0 : D0 = [] := hiff.mp hs_nil
          refine (WP.spec_ok _).mpr ?_
          have hr : NegResult toInt lo hi D0 (.Err { kind := .Empty }) := by
            unfold NegResult; exact ⟨.InvalidDigit, by simp [negRef, hD0], Or.inr rfl⟩
          exact SlotsOK_of_mem (by simp) hr (by simp)
        · have hhead : (↑s : List U8).head? = some val2 := ho.symm
          have hcons : (↑s : List U8) = val2 :: (↑s : List U8).tail := by
            apply cons_of_getElem?_zero
            rcases hl : (↑s : List U8) with _ | ⟨a', l⟩
            · rw [hl] at hhead; simp at hhead
            · rw [hl] at hhead; simpa using hhead
          have hlen_pos : 0 < s.val.length := by rw [hcons]; simp
          have hge : c ≤ s.val.length := by
            rcases hdisj with h' | h'
            · exact h'
            · omega
          have hne : D0 ≠ [] := by
            intro h0; have := hiff.mpr h0; rw [this] at hlen_pos; simp at hlen_pos
          obtain ⟨hchn, ha⟩ : ch = none ∧ a = 0 := by
            rcases hc : ch with _ | ⟨d2, t2'⟩
            · exact ⟨rfl, hnone hc⟩
            · exfalso; have := (hsome d2 t2' hc).2.2; omega
          subst ha
          step as ⟨val3, hval3⟩
          have hw := U8.wrapping_sub_48_val val2
          have hvb := U8.val_lt_256 val2
          have hdig := wrapping_digit_test val2.val hvb
          refine WP.spec_bind (Pₘ := NegPrePost toInt lo hi D0
            (fun c' => NegPreInv toInt lo hi c D0 c'.1 c'.2.2.1 ∧ c'.1.val.length < s.val.length)
            (¬ (s.val.length = c ∧ (val3.val : ℤ) ≤ (hi + 1) / 10 ^ (c - 1)))) ?_ ?_
          · refine WP.spec_ite (fun hlc => ?_) (fun hlc => ?_)
            · step as ⟨fs, hfs⟩
              refine WP.spec_ite (fun hle => ?_) (fun hgt => ?_)
              · -- a small first digit: set it aside with its weight
                have hslen : s.val.length = c := by
                  have := congrArg UScalar.val hlc; rw [Slice.len_val] at this; simp [Slice.length] at this; omega
                have hle' : (val3.val : ℤ) ≤ (hi + 1) / 10 ^ (c - 1) := by
                  have := (UScalar.le_equiv val3 fs).mp hle; omega
                have hfs9 := fs_le_9 hi c (by have := hF.hi_lt; omega) (by omega) hF.fs_mul_le
                have h9 : val3.val ≤ 9 := by omega
                have hv3d : (val3.val : ℤ) = (val2.val : ℤ) - 48 := by
                  rw [hval3, hw] at h9 ⊢; omega
                have hdd : isDigit val2 := by
                  show 48 ≤ val2.val ∧ val2.val ≤ 57; omega
                step as ⟨vt, hvt⟩
                have hvt' : toInt vt = (val3.val : ℤ) := hvt (by omega)
                step as ⟨tr, htrlen, htr⟩
                step as ⟨i3, hi3⟩
                have hi3c : i3.val = c - 1 := by omega
                step with Slice.index_usize_spec tr i3 (by simp only [Slice.length]; omega) as ⟨t2, ht2⟩
                have htv : toInt t2 = 10 ^ (c - 1) := by
                  rw [ht2]; simp only [hi3c]; exact htr _ (by omega)
                have hmulr : InRange lo hi (toInt vt * toInt t2) := by
                  rw [hvt', htv]
                  have hp : (0 : ℤ) ≤ 10 ^ (c - 1) := by positivity
                  have hp0 : (0 : ℤ) ≤ (val3.val : ℤ) * 10 ^ (c - 1) := by positivity
                  have := hF.fs_mul_le
                  refine ⟨by omega, ?_⟩
                  nlinarith
                step with hMul vt t2 hmulr as ⟨t3, ht3⟩
                step as ⟨s7, hs7, hs7len⟩
                show NegPreInv toInt lo hi c D0 s7 (some (val3, t3)) ∧ s7.val.length < s.val.length
                have hs7l : s7.val.length = c - 1 := by rw [hs7]; simp; omega
                have hfoldN : stdDigits lo hi true 0 D0 = stdDigits lo hi true (-(val3.val : ℤ)) s7.val := by
                  rw [hfold, hcons, stdDigits_neg_cons_digit lo hi 0 val2 _ hdd ⟨by omega, by omega⟩, hs7]
                  simp [hv3d]
                have hbndN : ∀ k, k < s7.val.length → k + 1 < c → lo ≤ -(val3.val : ℤ) * 10 ^ k - (10 ^ k - 1) := by
                  intro k hk _
                  rw [hs7l] at hk
                  have hp : (0 : ℤ) ≤ 10 ^ k := by positivity
                  have hk1 : (10 : ℤ) ^ (k + 1) ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
                  have := hF.hi_ge
                  rw [pow_succ] at hk1
                  nlinarith
                have hsomeN : ∀ d' t', some (val3, t3) = some (d', t') →
                    -(val3.val : ℤ) = -(d'.val : ℤ) ∧ toInt t' = (d'.val : ℤ) * 10 ^ s7.val.length ∧
                      s7.val.length + 1 = c := by
                  intro d' t' h'
                  cases h'
                  refine ⟨rfl, ?_, by omega⟩
                  rw [ht3, hvt', htv, hs7l]
                have hnoneN : some (val3, t3) = none → -(val3.val : ℤ) = 0 := fun h' => by cases h'
                refine ⟨⟨⟨-(val3.val : ℤ), by omega, by omega, hfoldN, hbndN, hnoneN, hsomeN⟩, ?_⟩, by omega⟩
                · constructor
                  · intro h'; rw [h'] at hs7l; simp at hs7l; omega
                  · intro h'; exact absurd h' hne
              · refine (WP.spec_ok _).mpr ?_
                intro h'
                apply hgt
                rw [UScalar.le_equiv]; omega
            · refine (WP.spec_ok _).mpr ?_
              intro h'
              apply hlc
              apply UScalar.eq_of_val_eq
              rw [Slice.len_val]; simp [Slice.length]; omega
          · rintro s5 hs5
            rcases s5 with (c' | e) | u
            · rcases c' with ⟨cs, cb, cch, cv, cv1, ci, ct1, ct2, ct3⟩
              exact (WP.spec_ok _).mpr hs5
            · rcases e with ⟨a1, a2, a3, a4, a5, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, a6, a7, a8, a9⟩
              exact (WP.spec_ok _).mpr hs5
            · have hnot1 : ¬ (s.val.length = c ∧ (val3.val : ℤ) ≤ (hi + 1) / 10 ^ (c - 1)) := hs5
              dsimp only
              refine WP.spec_ite (fun h0 => ?_) (fun hne0 => ?_)
              · -- a leading zero: strip the zeros
                have hv0 : val3.val = 0 := by rw [h0]; simp
                have h48 : (↑s : List U8)[0]? = some 48#u8 := by
                  rw [hval3, hw] at hv0
                  have : val2 = 48#u8 := by apply UScalar.eq_of_val_eq; simp; omega
                  rw [hcons, this]; simp
                step with parse_inner_loop0_loop0_loop1_spec hF s b ch v 48#u8 s.len i' t1 t2 t3 s hlen_pos h48
                  as ⟨s6, b2, ch2, v4, v5, l2, lr, i2, s7, s8, s9, s10, hpz⟩
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs10, hpz⟩ := hpz
                rcases hdz : dropZeros (↑s : List U8) with _ | ⟨d', rest⟩ <;> simp only [hdz] at hpz
                · -- all zeros: `Ok(0)`
                  obtain ⟨tt, hlr, htt⟩ := hpz
                  subst hlr
                  refine (WP.spec_ok _).mpr ?_
                  refine SlotsOK_of_mem (r := .Ok tt) (by simp) ?_ (by simp)
                  show negRef lo hi D0 = .ok (toInt tt)
                  rw [negRef_of_ne lo hi hne, hfold, htt]
                  exact stdDigits_neg_zeros lo hi _ hlo' (le_of_lt hF.hi_pos) hdz
                · -- a byte after the zeros: back to the top
                  obtain ⟨hs6, hlr, hv5⟩ := hpz
                  subst hlr
                  refine (WP.spec_ok _).mpr ?_
                  have hdz' : (↑s : List U8).dropWhile (fun b => decide (b = 48#u8)) = d' :: rest := hdz
                  refine ⟨⟨⟨0, le_refl 0, by omega, ?_, ?_, fun _ => rfl, ?_⟩, ?_⟩, ?_⟩
                  · rw [hfold, stdDigits_neg_dropZeros lo hi _ hlo' (le_of_lt hF.hi_pos), hdz', hs6]
                  · intro k hk
                    have hle : (dropZeros (↑s : List U8)).length ≤ (↑s : List U8).length :=
                      (List.dropWhile_sublist _).length_le
                    rw [hdz] at hle
                    rw [hs6] at hk
                    intro hkc
                    exact hbnd k (by simp at hle hk; omega) hkc
                  · intro d2 t2' h'; rw [hchn] at h'; cases h'
                  · constructor
                    · intro h'; rw [h'] at hs6; cases hs6
                    · intro h'; exact absurd h' hne
                  · rw [hs6, ← hdz]
                    have h1 := dropZeros_drop_of_48 _ h48
                    rw [h1]
                    calc (dropZeros (List.drop 1 ↑s)).length ≤ (List.drop 1 (↑s : List U8)).length :=
                          (List.dropWhile_sublist _).length_le
                      _ < (↑s : List U8).length := by simp; omega
              · -- a first digit too big, or too many digits: overflow
                have hv3ne : val3.val ≠ 0 := fun h' => hne0 (UScalar.eq_of_val_eq (by rw [h']; simp))
                refine (WP.spec_ok _).mpr ?_
                refine SlotsOK_of_mem (r := .Err { kind := .NegOverflow }) (by simp) ?_ (by simp)
                apply neg_pre_overflow hF hlo D0 s val2 hcons hne (by rw [hfold])
                by_cases hdd : isDigit val2
                · left
                  have hv3d : (val3.val : ℤ) = (val2.val : ℤ) - 48 := by
                    rw [hval3, hw]; have := hdd.1; omega
                  refine ⟨hdd, by omega, ?_⟩
                  by_cases hlc : s.val.length = c
                  · right; refine ⟨hlc, ?_⟩
                    have := fun h' => hnot1 ⟨hlc, h'⟩
                    omega
                  · left; omega
                · right; exact hdd
  · exact h

end atoi_radix10
