import Proofs.NegPre

/-!
The sign dispatch of `parse` (`src/parse.rs` lines 196-543, `parse_inner_loop0`): a digit first goes to
the positive path; a `-` on a signed type runs the negative path, whose 25 result slots are
cascaded into one; a `+` is skipped once and must be followed by a digit (else `Err(Empty)`,
where core says bad digit); anything else is `Err(InvalidDigit)`.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The claim of `ParseSpec` for one result. -/
def ParseResult {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) :
    core.result.Result T ParseIntErrorPublic → Prop
  | .Ok v => stdParse lo hi D0 = .ok (toInt v)
  | .Err e => ∃ k, stdParse lo hi D0 = .error k ∧ kindLike e.kind k

/-! ### `stdParse` by its first byte -/

theorem stdParse_digit_head (lo hi : ℤ) (d : U8) (rest : List U8) (hd : isDigit d) :
    stdParse lo hi (d :: rest) = stdDigits lo hi false 0 (d :: rest) := by
  have h43 : ¬ d.val = 43 := by have := hd.1; omega
  have h45 : ¬ d.val = 45 := by have := hd.1; omega
  rcases rest with _ | ⟨b, bs⟩
  · simp [stdParse, h43, h45]
  · simp [stdParse, h43, h45]

theorem stdParse_plus (lo hi : ℤ) (rest : List U8) (hne : rest ≠ []) :
    stdParse lo hi (43#u8 :: rest) = stdDigits lo hi false 0 rest := by
  rcases rest with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp [stdParse]

theorem stdParse_plus_nil (lo hi : ℤ) : stdParse lo hi [43#u8] = .error .InvalidDigit := by
  simp [stdParse]

theorem stdParse_minus (lo hi : ℤ) (hlo : lo < 0) (rest : List U8) :
    stdParse lo hi (45#u8 :: rest) = negRef lo hi rest := by
  rcases rest with _ | ⟨b, bs⟩
  · simp [stdParse, negRef]
  · simp [stdParse, negRef, hlo]

/-- A first byte that is neither a digit nor a sign that applies: `InvalidDigit`. -/
theorem stdParse_invalid_head (lo hi : ℤ) (d : U8) (rest : List U8) (hnd : ¬ isDigit d)
    (h43 : d.val ≠ 43) (h45 : d.val = 45 → ¬ lo < 0) :
    stdParse lo hi (d :: rest) = .error .InvalidDigit := by
  rcases rest with _ | ⟨b, bs⟩
  · by_cases h : d.val = 45
    · simp [stdParse, h]
    · simp [stdParse, h43, h, stdDigits, hnd]
  · by_cases h : d.val = 45
    · have := h45 h
      simp [stdParse, h, this, stdDigits, hnd]
    · simp [stdParse, h43, h, stdDigits, hnd]

theorem ParseResult_of_neg {T : Type} {toInt : T → ℤ} {lo hi : ℤ} (hlo : lo < 0) {D0 tail : List U8}
    (hD0 : D0 = 45#u8 :: tail) {r : core.result.Result T ParseIntErrorPublic}
    (h : NegResult toInt lo hi tail r) : ParseResult toInt lo hi D0 r := by
  rcases r with v | e
  · show stdParse lo hi D0 = .ok (toInt v)
    rw [hD0, stdParse_minus lo hi hlo]; exact h
  · obtain ⟨k, hk, hkl⟩ := h
    exact ⟨k, by rw [hD0, stdParse_minus lo hi hlo]; exact hk, hkl⟩

theorem MINUS_val : MINUS.val = 253 := by
  unfold MINUS; rw [U8.wrapping_sub_48_val]; simp
theorem PLUS_val : PLUS.val = 251 := by
  unfold PLUS; rw [U8.wrapping_sub_48_val]; simp

/-- The `done` payload of the sign loop. -/
abbrev SignDone (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 ×
  Option (core.result.Result T ParseIntErrorPublic) × Slice U8
/-- Its `cont` payload. -/
abbrev SignCont := Slice U8 × Bool × U8 × U8 × Slice U8

/-- What the sign loop hands over: a result, or the positive path's entry state. -/
def SignPost {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 : List U8) : SignDone T → Prop
  | (_, _, _, _, _, some r, _) => ParseResult toInt lo hi D0 r
  | (s', _, ch', _, v1', none, _) => ch' = none ∧ PreInv toInt lo hi c s'.val s' none v1' ∧
      stdParse lo hi D0 = stdDigits lo hi false 0 s'.val

/-- The join inside the body. -/
def SignCut {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 : List U8) (inrOK : Prop) :
    Sum (Sum SignCont (SignDone T)) Unit → Prop
  | .inl (.inl _) => False
  | .inl (.inr e) => SignPost toInt lo hi c D0 e
  | .inr _ => inrOK

/-- The byte under the digit test. -/
theorem wrap_le_9 (d v1 : U8) (hv : v1.val = (d.val + 256 - 48) % 256) :
    (v1 ≤ 9#u8 ↔ isDigit d) := by
  have hb := U8.val_lt_256 d
  have ht := wrapping_digit_test d.val hb
  have h9v : (9#u8).val = 9 := by simp
  rw [UScalar.le_equiv, hv, h9v]
  exact ht

set_option maxHeartbeats 4000000 in
theorem parse_inner_loop0_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (D0 : List U8) (t : T)
    (ht : toInt t = lo) (s : Slice U8) (is_signed_ty : Bool) (val val1 : U8) (s1 : Slice U8)
    (hsg : is_signed_ty = decide (lo < 0)) (hs : s.val = D0)
    (hd : ∃ d, s.val[0]? = some d ∧ val1.val = (d.val + 256 - 48) % 256) :
    parse.parse_inner_loop0 inst t s is_signed_ty val val1 s1
      ⦃ (out : SignDone T) => SignPost toInt lo hi c D0 out ⦄ := by
  unfold parse.parse_inner_loop0
  apply loop.spec_decr_nat (fun p : SignCont => p.1.val.length)
    (fun p : SignCont => match p with
      | (s', b, v, v1, t1) =>
        b = is_signed_ty ∧ (∃ d, s'.val[0]? = some d ∧ v1.val = (d.val + 256 - 48) % 256) ∧
        (s'.val = D0 ∨ (∃ rest d, D0 = 43#u8 :: rest ∧ s'.val = rest ∧ rest[0]? = some d ∧ isDigit d)))
  · rintro ⟨s', b, v, v1, t1⟩ ⟨rfl, ⟨d, hd0, hv1⟩, hcase⟩
    have hc3 := hF.three_le_c
    have hlo' := hF.lo_le
    have hdb := U8.val_lt_256 d
    have hcons := cons_of_getElem?_zero _ hd0
    have hdig := wrap_le_9 d v1 hv1
    have hhi9 : (9 : ℤ) ≤ hi := by
      have := hF.hi_ge
      have : (10 : ℤ) ^ 1 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    unfold parse.parse_inner_loop0.body
    refine WP.spec_ite (fun h9 => ?_) (fun h9 => ?_)
    · -- a digit: the positive path
      have hdd : isDigit d := hdig.mp h9
      refine (WP.spec_ok _).mpr ?_
      have hrel : stdParse lo hi D0 = stdDigits lo hi false 0 (↑s' : List U8) := by
        rcases hcase with hc | ⟨rest, d', hD0, hrest, hd', hdd'⟩
        · rw [← hc, hcons, stdParse_digit_head lo hi d _ hdd]
        · rw [hD0, hrest, stdParse_plus lo hi rest (by rw [hrest] at hcons; rw [hcons]; simp)]
      refine ⟨rfl, ⟨by rw [hcons]; simp, ⟨d, hd0, hdd, by rw [hv1]; have := hdd.1; omega⟩, 0, le_refl 0, by omega, rfl, ?_, fun _ => rfl, fun _ _ h => by cases h⟩, hrel⟩
      intro k _ hkc
      have h10 : (10 : ℤ) ^ k ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have := hF.hi_ge
      omega
    · have hnd : ¬ isDigit d := fun h => h9 (hdig.mpr h)
      -- after a `+`, the next byte is a digit: so this is the first byte of the input
      have hsD0 : (↑s' : List U8) = D0 := by
        rcases hcase with hc | ⟨rest, d', hD0, hrest, hd', hdd'⟩
        · exact hc
        · exfalso; rw [hrest] at hd0; rw [hd0] at hd'; cases hd'; exact hnd hdd'
      refine WP.spec_bind (Pₘ := SignCut toInt lo hi c D0 (b = true → ¬ v1 = MINUS)) ?_ ?_
      · refine WP.spec_ite (fun hsigned => ?_) (fun hunsigned => ?_)
        · refine WP.spec_ite (fun hminus => ?_) (fun hminus => ?_)
          · -- the negative path
            have hlo : lo < 0 := by rw [hsg] at hsigned; exact of_decide_eq_true hsigned
            have hd45 : d.val = 45 := by
              have := congrArg UScalar.val hminus; rw [hv1, MINUS_val] at this; omega
            have hD0m : D0 = 45#u8 :: (↑s' : List U8).tail := by
              rw [← hsD0, hcons]; congr 1; exact UScalar.eq_of_val_eq (by rw [hd45]; simp)
            step as ⟨s3, hs3, hs3len⟩
            have hs3' : (↑s3 : List U8) = (↑s' : List U8).tail := by rw [hs3]; simp
            have hpre : NegPreInv toInt lo hi c (↑s3 : List U8) s3 none := by
              refine ⟨⟨0, le_refl 0, hlo', rfl, ?_, fun _ => rfl, fun _ _ h => by cases h⟩, Iff.rfl⟩
              intro k _ hkc
              have h10 : (10 : ℤ) ^ k ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
              have := hF.hi_ge
              have := hF.signed hlo
              omega
            step with parse_inner_loop0_loop0_spec hF hlo (↑s3 : List U8) t ht s3 b none v v1 MINUS t1 s' s3 hpre as ⟨s4, b1, ch1, v2, v3, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, i2, s5, s6, s7, hpost⟩
            rw [hs3'] at hpost
            have hpost : SlotsOK (NegResult toInt lo hi (↑s' : List U8).tail) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25] := hpost
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
                                                      · rcases o23 with _ | r23
                                                        · rcases o24 with _ | r24
                                                          · rcases o25 with _ | r25
                                                            · exfalso
                                                              obtain ⟨⟨r, hr⟩, _⟩ := hpost
                                                              simp at hr
                                                            · refine (WP.spec_ok _).mpr ?_
                                                              exact ParseResult_of_neg hlo hD0m (hpost.2 r25 (by simp))
                                                          · refine (WP.spec_ok _).mpr ?_
                                                            exact ParseResult_of_neg hlo hD0m (hpost.2 r24 (by simp))
                                                        · refine (WP.spec_ok _).mpr ?_
                                                          exact ParseResult_of_neg hlo hD0m (hpost.2 r23 (by simp))
                                                      · refine (WP.spec_ok _).mpr ?_
                                                        exact ParseResult_of_neg hlo hD0m (hpost.2 r22 (by simp))
                                                    · refine (WP.spec_ok _).mpr ?_
                                                      exact ParseResult_of_neg hlo hD0m (hpost.2 r21 (by simp))
                                                  · refine (WP.spec_ok _).mpr ?_
                                                    exact ParseResult_of_neg hlo hD0m (hpost.2 r20 (by simp))
                                                · refine (WP.spec_ok _).mpr ?_
                                                  exact ParseResult_of_neg hlo hD0m (hpost.2 r19 (by simp))
                                              · refine (WP.spec_ok _).mpr ?_
                                                exact ParseResult_of_neg hlo hD0m (hpost.2 r18 (by simp))
                                            · refine (WP.spec_ok _).mpr ?_
                                              exact ParseResult_of_neg hlo hD0m (hpost.2 r17 (by simp))
                                          · refine (WP.spec_ok _).mpr ?_
                                            exact ParseResult_of_neg hlo hD0m (hpost.2 r16 (by simp))
                                        · refine (WP.spec_ok _).mpr ?_
                                          exact ParseResult_of_neg hlo hD0m (hpost.2 r15 (by simp))
                                      · refine (WP.spec_ok _).mpr ?_
                                        exact ParseResult_of_neg hlo hD0m (hpost.2 r14 (by simp))
                                    · refine (WP.spec_ok _).mpr ?_
                                      exact ParseResult_of_neg hlo hD0m (hpost.2 r13 (by simp))
                                  · refine (WP.spec_ok _).mpr ?_
                                    exact ParseResult_of_neg hlo hD0m (hpost.2 r12 (by simp))
                                · refine (WP.spec_ok _).mpr ?_
                                  exact ParseResult_of_neg hlo hD0m (hpost.2 r11 (by simp))
                              · refine (WP.spec_ok _).mpr ?_
                                exact ParseResult_of_neg hlo hD0m (hpost.2 r10 (by simp))
                            · refine (WP.spec_ok _).mpr ?_
                              exact ParseResult_of_neg hlo hD0m (hpost.2 r9 (by simp))
                          · refine (WP.spec_ok _).mpr ?_
                            exact ParseResult_of_neg hlo hD0m (hpost.2 r8 (by simp))
                        · refine (WP.spec_ok _).mpr ?_
                          exact ParseResult_of_neg hlo hD0m (hpost.2 r7 (by simp))
                      · refine (WP.spec_ok _).mpr ?_
                        exact ParseResult_of_neg hlo hD0m (hpost.2 r6 (by simp))
                    · refine (WP.spec_ok _).mpr ?_
                      exact ParseResult_of_neg hlo hD0m (hpost.2 r5 (by simp))
                  · refine (WP.spec_ok _).mpr ?_
                    exact ParseResult_of_neg hlo hD0m (hpost.2 r4 (by simp))
                · refine (WP.spec_ok _).mpr ?_
                  exact ParseResult_of_neg hlo hD0m (hpost.2 r3 (by simp))
              · refine (WP.spec_ok _).mpr ?_
                exact ParseResult_of_neg hlo hD0m (hpost.2 r2 (by simp))
            · refine (WP.spec_ok _).mpr ?_
              exact ParseResult_of_neg hlo hD0m (hpost.2 r1 (by simp))
          · refine (WP.spec_ok _).mpr ?_
            exact fun _ => hminus
        · refine (WP.spec_ok _).mpr ?_
          exact fun h => absurd h hunsigned
      · rintro s2 hs2
        rcases s2 with (c' | e) | u
        · exact (hs2 : False).elim
        · rcases e with ⟨e1, e2, e3, e4, e5, e6, e7⟩
          exact (WP.spec_ok _).mpr hs2
        · have hnm : b = true → ¬ v1 = MINUS := hs2
          dsimp only
          refine WP.spec_ite (fun hplus => ?_) (fun hplus => ?_)
          · -- a `+`: skip it, a digit must follow
            have hd43 : d.val = 43 := by
              have := congrArg UScalar.val hplus; rw [hv1, PLUS_val] at this; omega
            have hD0p : D0 = 43#u8 :: (↑s' : List U8).tail := by
              rw [← hsD0, hcons]; congr 1; exact UScalar.eq_of_val_eq (by rw [hd43]; simp)
            step as ⟨s3, hs3, hs3len⟩
            have hs3' : (↑s3 : List U8) = (↑s' : List U8).tail := by rw [hs3]; simp
            step as ⟨o, ho⟩
            rcases o with _ | value
            · -- nothing follows
              have hnil : (↑s3 : List U8) = [] := List.head?_eq_none_iff.mp ho.symm
              refine (WP.spec_ok _).mpr ?_
              refine ⟨.InvalidDigit, ?_, Or.inr rfl⟩
              rw [hD0p, ← hs3', hnil, stdParse_plus_nil]
            · have hhead : (↑s3 : List U8).head? = some value := ho.symm
              have hcons3 : (↑s3 : List U8) = value :: (↑s3 : List U8).tail := by
                apply cons_of_getElem?_zero
                rcases hl : (↑s3 : List U8) with _ | ⟨a', l⟩
                · rw [hl] at hhead; simp at hhead
                · rw [hl] at hhead; simpa using hhead
              step as ⟨value1, hvalue1⟩
              have hw := U8.wrapping_sub_48_val value
              have hdig' := wrap_le_9 value value1 (by rw [hvalue1, hw])
              refine WP.spec_ite (fun h9' => ?_) (fun h9' => ?_)
              · -- a digit: round again, and the digit test will hand over
                refine (WP.spec_ok _).mpr ?_
                refine ⟨rfl, ⟨value, by rw [hcons3]; simp, by rw [hvalue1, hw]⟩, Or.inr ⟨(↑s3 : List U8), value, by rw [hD0p, hs3'], rfl, by rw [hcons3]; simp, hdig'.mp h9'⟩, ?_⟩
                rw [hs3']; simp; rw [hcons]; simp
              · -- not a digit after the `+`
                have hnd' : ¬ isDigit value := fun h => h9' (hdig'.mpr h)
                refine (WP.spec_ok _).mpr ?_
                refine ⟨.InvalidDigit, ?_, Or.inr rfl⟩
                rw [hD0p, ← hs3', stdParse_plus lo hi _ (by rw [hcons3]; simp), hcons3,
                  stdDigits_nonDigit lo hi false 0 value _ hnd']
          · -- neither a digit nor a sign that applies
            refine (WP.spec_ok _).mpr ?_
            refine ⟨.InvalidDigit, ?_, Or.inl rfl⟩
            rw [← hsD0, hcons]
            apply stdParse_invalid_head lo hi d _ hnd
            · intro h43; apply hplus; apply UScalar.eq_of_val_eq; rw [hv1, PLUS_val, h43]
            · intro h45 hlo
              have hsigned : b = true := by rw [hsg]; exact decide_eq_true hlo
              apply hnm hsigned; apply UScalar.eq_of_val_eq; rw [hv1, MINUS_val, h45]
  · obtain ⟨d, hd0, hv1⟩ := hd
    exact ⟨rfl, ⟨d, hd0, hv1⟩, Or.inl hs⟩

end atoi_radix10
