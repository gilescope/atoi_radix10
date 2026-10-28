import Proofs.Sign

/-!
`parse<T>` meets `ParseSpec` for every faithful instance: the sign dispatch (`parse_loop0_spec`,
with the whole negative path inside it), then the positive pre-pass (`parse_loop1_spec`) and the
positive SWAR block (`parse_loop2_spec`). `parse_spec_u8` is the theorem for `u8`.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

theorem PosResult_to_ParseResult {T : Type} {toInt : T → ℤ} {lo hi : ℤ} {D0 D : List U8}
    (hrel : stdParse lo hi D0 = stdDigits lo hi false 0 D) {r : core.result.Result T ParseIntErrorPublic}
    (h : PosResult toInt lo hi D r) : ParseResult toInt lo hi D0 r := by
  rcases r with v | e
  · show stdParse lo hi D0 = .ok (toInt v)
    rw [hrel]; exact h
  · obtain ⟨k, hk, hkl⟩ := h
    exact ⟨k, by rw [hrel]; exact hk, hkl⟩

theorem parse_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ} {lo hi : ℤ}
    {c : ℕ} (hF : Faithful inst toInt lo hi c) : ParseSpec inst toInt lo hi := by
  intro s
  have hF32 := hF.from_u32
  have hMIN := hF.MIN
  have hGT := hF.gt
  have hF8 := hF.from_u8
  unfold parse.parse
  step as ⟨t, ht⟩
  have ht0 : toInt t = 0 := by
    have := ht (by simp; exact le_of_lt hF.hi_pos); simpa using this
  step as ⟨t1, ht1⟩
  step as ⟨b, hb⟩
  have hsg : b = decide (lo < 0) := by rw [hb, ht1, ht0]
  step as ⟨o, ho⟩
  rcases o with _ | val
  · -- nothing at all: `Err(Empty)`
    have hnil : (↑s : List U8) = [] := List.head?_eq_none_iff.mp ho.symm
    rw [WP.spec_ok]
    show ∃ k, stdParse lo hi (↑s : List U8) = .error k ∧ kindLike .Empty k
    exact ⟨.Empty, by rw [hnil]; rfl, Or.inl rfl⟩
  · have hhead : (↑s : List U8).head? = some val := ho.symm
    have hd0 : (↑s : List U8)[0]? = some val := by
      rcases hl : (↑s : List U8) with _ | ⟨a', l⟩
      · rw [hl] at hhead; simp at hhead
      · rw [hl] at hhead; simpa using hhead
    step as ⟨val1, hval1⟩
    step with parse_loop0_spec hF (↑s : List U8) t1 ht1 s b val val1 s hsg rfl
      ⟨val, hd0, by rw [hval1, U8.wrapping_sub_48_val]⟩ as ⟨s1, b1, ch, v2, v3, lr, s2, hpost⟩
    rcases lr with _ | r
    · -- the positive path
      obtain ⟨hchn, hpre, hrel⟩ := hpost
      subst hchn
      step with parse_loop1_spec hF s1 b1 none v2 v3 s2 s1 hpre as ⟨s3, b2, ch1, v4, v5, lr1, s4, s5, hpost1⟩
      obtain ⟨rfl, rfl, rfl, rfl, hres⟩ := hpost1
      rcases lr1 with _ | r
      · -- the SWAR block
        obtain ⟨hpre1, hlt⟩ := hres
        step as ⟨res, hres0⟩
        have hres0' : toInt res = 0 := by
          have := hres0 (by simp; exact le_of_lt hF.hi_pos); simpa using this
        apply WP.spec_mono_post (parse_loop2_spec hF (↑s5 : List U8) s3 b2 ch1 v4 v5 res s4 s5 s3
          (Handover.of_pre hpre1 hlt) hres0' hpre1.head)
        intro r hr
        exact PosResult_to_ParseResult hrel hr
      · -- the pre-pass answered
        rw [WP.spec_ok]
        exact PosResult_to_ParseResult hrel hres
    · -- the sign loop answered: a negative number, or an error
      rw [WP.spec_ok]
      exact hpost

/-- `parse::<u8>` meets core's `str::parse::<u8>`, values read as naturals in `[0, 255]`. -/
theorem parse_spec_u8 : ParseSpec U8F.inst (fun x : U8 => (x.val : ℤ)) 0 255 :=
  parse_spec faithful_u8

end atoi_radix10
