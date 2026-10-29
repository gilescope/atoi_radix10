import Proofs.Final

/-!
`std_error_kind`, the cold classifier `parse` runs on the error path, computes core's error kind:
`Empty`, `InvalidDigit` for a lone sign, and otherwise core's fold over the digits with no value
kept, stopping at the first bad byte or the first overflow. `std_error_kind_spec` says it
returns the kind `stdParse` reports, for any input `stdParse` rejects; `parse_spec` then
tightens `parse_inner_spec`'s `kindLike` to equality. The loop's exit when every digit fitted
is unreachable (core would have accepted), which is why `KindInv` carries the failing fold.

-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The loop's invariant: the accumulator has the fold's sign, and the fold of what is left
errs with `k`. -/
def KindInv {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (neg : Bool) (D : List U8) (k : Kind)
    (st : T × Usize) : Prop :=
  (if neg then InRange lo 0 (toInt st.1) else InRange 0 hi (toInt st.1)) ∧
  st.2.val ≤ D.length ∧ stdDigits lo hi neg (toInt st.1) (D.drop st.2.val) = .error k

@[step]
theorem overflow_spec (neg : Bool) :
    parse.overflow neg ⦃ e => e.kind = if neg then .NegOverflow else .PosOverflow ⦄ := by
  cases neg <;> simp [parse.overflow, WP.spec_ok]

theorem std_error_kind_loop_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (digits : Slice U8) (neg : Bool)
    (ten acc : T) (i : Usize) (k : Kind) (hten : toInt ten = 10)
    (hinv : KindInv toInt lo hi neg digits.val k (acc, i)) :
    parse.std_error_kind_loop inst digits neg ten acc i ⦃ e => e.kind = k ⦄ := by
  unfold parse.std_error_kind_loop
  apply loop.spec_decr_nat (fun st : T × Usize => digits.val.length - st.2.val)
    (KindInv toInt lo hi neg digits.val k)
  · rintro ⟨a, j⟩ ⟨hsign, hle, herr⟩
    simp only at hsign hle herr
    unfold parse.std_error_kind_loop.body
    have hlo := hF.lo_le
    have hhi := hF.hi_pos
    have hF8 := hF.from_u8
    have hmul := hF.mul_checked
    have hadd := hF.add_checked
    have hsub := hF.sub_checked
    by_cases hlt : j.val < digits.val.length
    · have hlt' : ¬ j ≥ Slice.len digits := by
        simp only [ge_iff_le, UScalar.le_equiv, Slice.len_val]; simp [Slice.length]; omega
      dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false hlt')]
      have hdrop := List.drop_eq_getElem_cons (l := digits.val) hlt
      rw [hdrop] at herr
      have hb256 : (digits.val[j.val]).val < 256 := by scalar_tac
      have hw := U8.wrapping_sub_48_val digits.val[j.val]
      have hdig := wrapping_digit_test (digits.val[j.val]).val hb256
      have h9v : (9#u8).val = 9 := by decide +kernel
      step as ⟨b, hb⟩
      subst hb
      step as ⟨d, hd⟩
      by_cases hgt : d > 9#u8
      · -- not a digit: core says `InvalidDigit`
        rw [ite_eq_left_of_eq_true _ _ (eq_true hgt)]
        have h9 : (9#u8).val < d.val := hgt
        rw [h9v, hd, hw] at h9
        have hnd : ¬ isDigit digits.val[j.val] := by
          show ¬ (48 ≤ (digits.val[j.val]).val ∧ (digits.val[j.val]).val ≤ 57); omega
        rw [stdDigits_nonDigit _ _ _ _ _ _ hnd] at herr
        rw [WP.spec_ok]
        show core.num.error.IntErrorKind.InvalidDigit = k
        exact Except.error.inj herr
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgt)]
        have h9 : ¬ (9#u8).val < d.val := hgt
        rw [h9v, hd, hw] at h9
        have hdg : isDigit digits.val[j.val] := by
          show 48 ≤ (digits.val[j.val]).val ∧ (digits.val[j.val]).val ≤ 57; omega
        have hdv : (d.val : ℤ) = ((digits.val[j.val]).val : ℤ) - 48 := by rw [hd, hw]; omega
        have hd9 : (d.val : ℤ) ≤ hi := by
          have := hF.hi_ge; have := hF.three_le_c
          have : (10 : ℤ) ^ 2 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          omega
        step as ⟨d1, hd1⟩
        have hd1v : toInt d1 = ((digits.val[j.val]).val : ℤ) - 48 := by rw [hd1 hd9, hdv]
        step as ⟨o, ho⟩
        rw [hten] at ho
        set bv : ℤ := ((digits.val[j.val]).val : ℤ) - 48 with hbv
        have hbv0 : 0 ≤ bv := by omega
        have hbv9 : bv ≤ 9 := by omega
        rcases o with _ | m
        · -- `acc * 10` overflows: so does the fold's step
          simp only [CheckedIs, InRange] at ho
          step as ⟨e, he⟩
          rw [he]
          cases neg
          · simp only [InRange, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
            rw [stdDigits_cons _ _ _ _ _ hdg, ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at herr
            exact Except.error.inj herr
          · simp only [InRange, ↓reduceIte] at hsign ⊢
            rw [stdDigits_neg_cons _ _ _ _ _ hdg, ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at herr
            exact Except.error.inj herr
        · simp only [CheckedIs, InRange] at ho
          obtain ⟨_, hm⟩ := ho
          cases neg
          · simp only [InRange, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
            step as ⟨o1, ho1⟩
            rw [hm, hd1v] at ho1
            rcases o1 with _ | v
            · simp only [CheckedIs, InRange] at ho1
              step as ⟨e, he⟩
              rw [he, stdDigits_cons _ _ _ _ _ hdg, ite_eq_right_of_eq_false _ _ (eq_false ho1)] at *
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact Except.error.inj herr
            · simp only [CheckedIs, InRange] at ho1
              obtain ⟨hr, hv⟩ := ho1
              step as ⟨j1, hj1⟩
              simp only [KindInv, InRange, Bool.false_eq_true, ↓reduceIte]
              refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
              · rw [hv]; omega
              · rw [hv]; exact hr.2
              · omega
              · rw [stdDigits_cons _ _ _ _ _ hdg, ite_eq_left_of_eq_true _ _ (eq_true hr), ← hv] at herr; rwa [hj1]
              · omega
          · simp only [InRange, ↓reduceIte] at hsign ⊢
            step as ⟨o1, ho1⟩
            rw [hm, hd1v] at ho1
            rcases o1 with _ | v
            · simp only [CheckedIs, InRange] at ho1
              step as ⟨e, he⟩
              rw [he, stdDigits_neg_cons _ _ _ _ _ hdg, ite_eq_right_of_eq_false _ _ (eq_false ho1)] at *
              simp only [↓reduceIte]
              exact Except.error.inj herr
            · simp only [CheckedIs, InRange] at ho1
              obtain ⟨hr, hv⟩ := ho1
              step as ⟨j1, hj1⟩
              simp only [KindInv, InRange, ↓reduceIte]
              refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
              · rw [hv]; exact hr.1
              · rw [hv]; omega
              · omega
              · rw [stdDigits_neg_cons _ _ _ _ _ hdg, ite_eq_left_of_eq_true _ _ (eq_true hr), ← hv] at herr; rwa [hj1]
              · omega
    · -- every digit fitted: core accepts, contradicting `herr`
      exfalso
      have hj : j.val = digits.val.length := by omega
      rw [hj, List.drop_length] at herr
      simp [stdDigits] at herr
  · exact hinv

theorem stdParse_sign_nil (lo hi : ℤ) (b : U8) (hb : b.val = 43 ∨ b.val = 45) :
    stdParse lo hi [b] = .error .InvalidDigit := by
  simp [stdParse, hb]

theorem stdParse_minus_signed (lo hi : ℤ) (hlo : lo < 0) (rest : List U8) (hne : rest ≠ []) :
    stdParse lo hi (45#u8 :: rest) = stdDigits lo hi true 0 rest := by
  rcases rest with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp [stdParse, hlo]

theorem stdParse_minus_unsigned (lo hi : ℤ) (hlo : ¬ lo < 0) (rest : List U8) (hne : rest ≠ []) :
    stdParse lo hi (45#u8 :: rest) = stdDigits lo hi false 0 (45#u8 :: rest) := by
  rcases rest with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp [stdParse, hlo]

theorem stdParse_other (lo hi : ℤ) (b : U8) (rest : List U8) (h43 : b.val ≠ 43) (h45 : b.val ≠ 45) :
    stdParse lo hi (b :: rest) = stdDigits lo hi false 0 (b :: rest) := by
  rcases rest with _ | ⟨b', bs⟩
  · simp [stdParse, h43, h45]
  · simp [stdParse, h43, h45]

/-- The classifier returns the kind core reports, on any input core rejects. -/
theorem std_error_kind_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (s : Slice U8) (k : Kind)
    (herr : stdParse lo hi s.val = .error k) :
    parse.std_error_kind inst s ⦃ e => e.kind = k ⦄ := by
  have hlo := hF.lo_le
  have hhi := hF.hi_pos
  have hF8 := hF.from_u8
  have hF32 := hF.from_u32
  have hMIN := hF.MIN
  have hGT := hF.gt
  have h10 : (10 : ℤ) ≤ hi := by
    have := hF.hi_ge; have := hF.three_le_c
    have : (10 : ℤ) ^ 2 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  unfold parse.std_error_kind
  step as ⟨t, ht⟩
  have ht0 : toInt t = 0 := by
    have := ht (by simp; exact le_of_lt hF.hi_pos); simpa using this
  step as ⟨t1, ht1⟩
  step as ⟨sg, hsg⟩
  have hsg' : sg = decide (lo < 0) := by rw [hsg, ht1, ht0]
  step as ⟨o, ho⟩
  rcases o with _ | b
  · -- empty input
    have hnil : s.val = [] := List.head?_eq_none_iff.mp ho.symm
    rw [WP.spec_ok]
    rw [hnil] at herr
    simp [stdParse] at herr
    exact herr
  · have hhead : s.val.head? = some b := ho.symm
    obtain ⟨rest, hs⟩ : ∃ rest, s.val = b :: rest := by
      rcases hl : s.val with _ | ⟨a', l⟩
      · rw [hl] at hhead; simp at hhead
      · rw [hl] at hhead; simp at hhead; exact ⟨l, by rw [hhead]⟩
    have hlen : (Slice.len s).val = rest.length + 1 := by rw [Slice.len_val]; simp [Slice.length, hs]
    have hlen1 : Slice.len s = 1#usize ↔ rest = [] := by
      constructor
      · intro h; have := congrArg UScalar.val h; rw [hlen] at this; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; rw [hlen, h]; simp
    have hten := hF8 10#u8
    have hzero := hF8 0#u8
    -- the loop, from the start, over `digits` with sign `neg`
    have hloop : ∀ (digits : Slice U8) (neg : Bool),
        stdDigits lo hi neg 0 digits.val = .error k →
        (do
          let ten ← inst.from_u8 10#u8
          let acc ← inst.from_u8 0#u8
          parse.std_error_kind_loop inst digits neg ten acc 0#usize) ⦃ e => e.kind = k ⦄ := by
      intro digits neg hd
      step as ⟨ten, hten'⟩
      step as ⟨acc, hacc⟩
      have hten10 : toInt ten = 10 := by rw [hten' (by simp; exact h10)]; simp
      have hacc0 : toInt acc = 0 := by rw [hacc (by simp; exact le_of_lt hhi)]; simp
      apply std_error_kind_loop_spec hF digits neg ten acc 0#usize k hten10
      refine ⟨?_, by simp, ?_⟩
      · cases neg <;> simp [InRange, hacc0, hlo, le_of_lt hhi]
      · simpa [hacc0] using hd
    dsimp only
    have hstart : (1#usize).val ≤ s.length := by simp [Slice.length, hs]
    split
    · -- `+`
      by_cases h1 : Slice.len s = 1#usize
      · have hr : rest = [] := hlen1.mp h1
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        step*
        rw [hs, hr, stdParse_sign_nil lo hi _ (Or.inl rfl)] at herr
        exact Except.error.inj herr
      · have hr : rest ≠ [] := fun h => h1 (hlen1.mpr h)
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        step as ⟨s2, hs2, _⟩
        apply hloop s2 false
        have hd : s2.val = rest := by simp [hs2, hs]
        rw [hd]
        rw [hs, show (43#8#uscalar : U8) = 43#u8 from rfl, stdParse_plus lo hi rest hr] at herr
        exact herr
    · -- `-`
      by_cases h1 : Slice.len s = 1#usize
      · have hr : rest = [] := hlen1.mp h1
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        step*
        rw [hs, hr, stdParse_sign_nil lo hi _ (Or.inr rfl)] at herr
        exact Except.error.inj herr
      · have hr : rest ≠ [] := fun h => h1 (hlen1.mpr h)
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1), hsg']
        by_cases hneg : lo < 0
        · simp only [hneg, decide_true, ↓reduceIte]
          step as ⟨s2, hs2, _⟩
          apply hloop s2 true
          have hd : s2.val = rest := by simp [hs2, hs]
          rw [hd]
          rw [hs, show (45#8#uscalar : U8) = 45#u8 from rfl, stdParse_minus_signed lo hi hneg rest hr] at herr
          exact herr
        · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
          refine hloop s false ?_
          rw [hs, show (45#8#uscalar : U8) = 45#u8 from rfl] at herr ⊢
          rw [stdParse_minus_unsigned lo hi hneg rest hr] at herr
          exact herr
    · -- anything else
      rename_i x h43 h45
      simp only [bind_ok]
      refine hloop s false ?_
      have h43v : b.val ≠ 43 := fun h => h43 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have h45v : b.val ≠ 45 := fun h => h45 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [hs, stdParse_other lo hi b rest h43v h45v] at herr
      rw [hs]
      exact herr


/-- `parse<T>` is core's `str::parse::<T>` for every faithful instance: `parse_inner` decides
`Ok`/`Err` and the value, `std_error_kind` the kind. -/
theorem parse_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ} {lo hi : ℤ}
    {c : ℕ} (hF : Faithful inst toInt lo hi c) : ParseSpec inst toInt lo hi := by
  intro s
  unfold parse.parse
  apply WP.spec_bind (parse_inner_spec hF s)
  intro r hr
  rcases r with v | e
  · rw [WP.spec_ok]; exact hr
  · obtain ⟨k, hk, _⟩ := hr
    apply WP.spec_bind (std_error_kind_spec hF s k hk)
    intro e' he'
    rw [WP.spec_ok]
    show stdParse lo hi s.val = .error e'.kind
    rw [he']; exact hk

/-- `parse::<u8>` meets core's `str::parse::<u8>`, values read as naturals in `[0, 255]`. -/
theorem parse_spec_u8 : ParseSpec U8F.inst (fun x : U8 => (x.val : ℤ)) 0 255 :=
  parse_spec faithful_u8

end atoi_radix10
