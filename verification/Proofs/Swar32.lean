import Proofs.Swar16

/-!
`parse_32_chars` (`src/lib.rs`): two `parse_16_chars`, the first scaled by `10^16`; an
`Err` from either is returned as is (the `?`).
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

theorem decimal_append (xs ys : List U8) :
    decimal (xs ++ ys) = decimal xs * 10 ^ ys.length + decimal ys := by
  induction xs with
  | nil => simp [decimal]
  | cons x xs ih => simp only [List.cons_append, decimal, ih, List.length_append]; ring

/-- `n` digits are below `10^n`. -/
theorem decimal_lt (l : List U8) (h : ∀ b ∈ l, isDigit b) : decimal l < 10 ^ l.length := by
  induction l with
  | nil => simp [decimal]
  | cons b l ih =>
    have hb := h b (by simp)
    have ih' := ih (fun b hb => h b (by simp [hb]))
    simp only [decimal, List.length_cons, pow_succ]
    have : b.val - 48 ≤ 9 := by have := hb.2; omega
    nlinarith

attribute [step] parse_16_chars_spec

/-- `parse_32_chars`: on a slice of at least 32 bytes, `Ok` of their decimal value exactly when
all 32 are ASCII digits, `Err(InvalidDigit)` otherwise. -/
theorem parse_32_chars_spec (s : Slice U8) (h : 32 ≤ s.val.length) :
    parse_32_chars s ⦃ out =>
      match out with
      | .Ok v => (∀ b ∈ s.val.take 32, isDigit b) ∧ v.val = decimal (s.val.take 32)
      | .Err e => ¬ (∀ b ∈ s.val.take 32, isDigit b) ∧ e.kind = .InvalidDigit ⦄ := by
  have hsplit : s.val.take 32 = s.val.take 16 ++ (s.val.drop 16).take 16 := by
    rw [← List.take_add]
  have hdig : (∀ b ∈ s.val.take 32, isDigit b) ↔
      (∀ b ∈ s.val.take 16, isDigit b) ∧ (∀ b ∈ (s.val.drop 16).take 16, isDigit b) := by
    rw [hsplit, List.forall_mem_append]
  have hlen16 : ((s.val.drop 16).take 16).length = 16 := by simp; omega
  unfold parse_32_chars
  step*
  · -- both halves are digits
    have hcf := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
    have hcf1 := ‹cf1 = core.ops.control_flow.ControlFlow.Continue val1›
    cases r with
    | Err e' =>
      dsimp only at cf_post
      rw [hcf] at cf_post
      cases cf_post
    | Ok v' =>
      cases r1 with
      | Err e1 =>
        dsimp only at cf1_post
        rw [hcf1] at cf1_post
        cases cf1_post
      | Ok v1' =>
        dsimp only at cf_post cf1_post r_post r1_post
        rw [hcf] at cf_post
        rw [hcf1] at cf1_post
        injection cf_post with hv
        injection cf1_post with hv1
        subst hv hv1
        obtain ⟨hd1, hv1⟩ := r_post
        obtain ⟨hd2, hv2⟩ := r1_post
        rw [s1_post] at hd2 hv2
        have hval16 : val16.val = val.val := by
          rw [val16_post, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (by scalar_tac)
        have hval161 : val161.val = val1.val := by
          rw [val161_post, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (by scalar_tac)
        refine ⟨hdig.mpr ⟨hd1, hd2⟩, ?_⟩
        rw [i1_post, res_post, hval16, hval161, hv1, hv2, hsplit, decimal_append, hlen16]
        ring
  · -- the second half is not
    have hcf1 := ‹cf1 = core.ops.control_flow.ControlFlow.Break residual›
    cases r1 with
    | Ok v1' =>
      dsimp only at cf1_post
      rw [hcf1] at cf1_post
      cases cf1_post
    | Err e1 =>
      dsimp only at cf1_post r1_post
      rw [hcf1, residual_post] at cf1_post
      injection cf1_post with he
      injection he with he
      subst he e_post
      subst ‹_ = core.result.Result.Err _›
      obtain ⟨hd2, hk⟩ := r1_post
      rw [s1_post] at hd2
      exact ⟨fun hd => hd2 (hdig.mp hd).2, hk⟩
  · -- the first half is not
    have hcf := ‹cf = core.ops.control_flow.ControlFlow.Break residual›
    cases r with
    | Ok v' =>
      dsimp only at cf_post
      rw [hcf] at cf_post
      cases cf_post
    | Err e1 =>
      dsimp only at cf_post r_post
      rw [hcf, residual_post] at cf_post
      injection cf_post with he
      injection he with he
      subst he e_post
      subst ‹_ = core.result.Result.Err _›
      obtain ⟨hd1, hk⟩ := r_post
      exact ⟨fun hd => hd1 (hdig.mp hd).1, hk⟩

end atoi_radix10
