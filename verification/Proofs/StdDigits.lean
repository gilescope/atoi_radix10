import Proofs.Ref

/-!
Facts about the reference fold `stdDigits`, for the positive path (`neg = false`): how it
behaves on a leading `'0'`, on a non-digit, when the accumulator is already too large, and
its closed form when no proper prefix can overflow, which is the situation the SWAR block
runs in.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- Every byte is an ASCII digit. -/
abbrev allDigits (l : List U8) : Prop := ∀ b ∈ l, isDigit b

instance : DecidablePred allDigits := fun l => inferInstanceAs (Decidable (∀ b ∈ l, isDigit b))

theorem decimal_cons (b : U8) (bs : List U8) :
    decimal (b :: bs) = (b.val - 48) * 10 ^ bs.length + decimal bs := rfl

theorem digit_sub48_nonneg {b : U8} (h : isDigit b) : (0 : ℤ) ≤ (b.val : ℤ) - 48 := by
  have := h.1; omega

theorem digit_sub48_le9 {b : U8} (h : isDigit b) : (b.val : ℤ) - 48 ≤ 9 := by
  have := h.2; omega

/-- Unfolding one step of the positive fold on a digit. -/
theorem stdDigits_cons (lo hi a : ℤ) (b : U8) (l : List U8) (hb : isDigit b) :
    stdDigits lo hi false a (b :: l) =
      if lo ≤ a * 10 + ((b.val : ℤ) - 48) ∧ a * 10 + ((b.val : ℤ) - 48) ≤ hi
      then stdDigits lo hi false (a * 10 + ((b.val : ℤ) - 48)) l
      else .error .PosOverflow := by
  simp [stdDigits, hb]

/-- A leading `'0'` changes nothing. -/
theorem stdDigits_cons_zero (lo hi : ℤ) (l : List U8) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    stdDigits lo hi false 0 (48#u8 :: l) = stdDigits lo hi false 0 l := by
  have h48 : isDigit 48#u8 := by show 48 ≤ (48#u8).val ∧ (48#u8).val ≤ 57; simp
  rw [stdDigits_cons lo hi 0 48#u8 l h48]
  simp [hlo, hhi]

/-- A non-digit at the head is `InvalidDigit`, whatever came before. -/
theorem stdDigits_nonDigit (lo hi : ℤ) (neg : Bool) (a : ℤ) (b : U8) (l : List U8)
    (h : ¬ isDigit b) : stdDigits lo hi neg a (b :: l) = .error .InvalidDigit := by
  simp [stdDigits, h]

/-- Folding one digit in, when the new accumulator is in range. -/
theorem stdDigits_cons_digit (lo hi a : ℤ) (b : U8) (l : List U8) (hb : isDigit b)
    (hr : lo ≤ a * 10 + ((b.val : ℤ) - 48) ∧ a * 10 + ((b.val : ℤ) - 48) ≤ hi) :
    stdDigits lo hi false a (b :: l) = stdDigits lo hi false (a * 10 + ((b.val : ℤ) - 48)) l := by
  rw [stdDigits_cons lo hi a b l hb]; simp [hr]

/-- An `ok` answer is at least `a · 10^len`, and at most `hi` when there was a digit. -/
theorem stdDigits_ok_bounds (lo hi : ℤ) (a : ℤ) (l : List U8) (v : ℤ) (ha : 0 ≤ a)
    (h : stdDigits lo hi false a l = .ok v) : a * 10 ^ l.length ≤ v ∧ (l ≠ [] → v ≤ hi) := by
  induction l generalizing a with
  | nil =>
    simp [stdDigits] at h
    simp [h]
  | cons b bs ih =>
    by_cases hb : isDigit b
    · have hd := digit_sub48_nonneg hb
      rw [stdDigits_cons lo hi a b bs hb] at h
      split_ifs at h with hr
      · obtain ⟨h1, h2⟩ := ih _ (by omega) h
        refine ⟨?_, fun _ => ?_⟩
        · rw [List.length_cons, pow_succ]
          have hp : (0 : ℤ) ≤ 10 ^ bs.length := by positivity
          nlinarith
        · rcases bs with _ | ⟨c, cs⟩
          · simp [stdDigits] at h; omega
          · exact h2 (by simp)
    · rw [stdDigits_nonDigit lo hi false a b bs hb] at h
      simp at h

/-- Too many digits for the type: never `ok`. -/
theorem stdDigits_long_err (lo hi a : ℤ) (c : ℕ) (l : List U8) (ha : 1 ≤ a) (hc : hi < 10 ^ c)
    (hc1 : 1 ≤ c) (hl : c ≤ l.length) : ∃ k, stdDigits lo hi false a l = .error k := by
  rcases h : stdDigits lo hi false a l with k | v
  · exact ⟨k, rfl⟩
  · exfalso
    obtain ⟨h1, h2⟩ := stdDigits_ok_bounds lo hi a l v (by omega) h
    have hne : l ≠ [] := by
      rintro rfl
      simp at hl; omega
    have h3 := h2 hne
    have h4 : (10 : ℤ) ^ c ≤ 10 ^ l.length := pow_le_pow_right₀ (by norm_num) hl
    have h5 : (10 : ℤ) ^ l.length ≤ a * 10 ^ l.length := by
      have : (0 : ℤ) ≤ 10 ^ l.length := by positivity
      nlinarith
    omega

/-- When no proper prefix can overflow (`hb`: the largest value after `k` more digits still fits
for every `k` short of the whole), the fold is the obvious thing: `InvalidDigit` if some byte is
not a digit, else the number, or `PosOverflow` if it does not fit. -/
theorem stdDigits_closed (lo hi a : ℤ) (l : List U8) (ha : 0 ≤ a) (hlo : lo ≤ 0) (hahi : a ≤ hi)
    (hb : ∀ k, k < l.length → a * 10 ^ k + (10 ^ k - 1) ≤ hi) :
    stdDigits lo hi false a l =
      if allDigits l then
        (if a * 10 ^ l.length + (decimal l : ℤ) ≤ hi
          then .ok (a * 10 ^ l.length + (decimal l : ℤ)) else .error .PosOverflow)
      else .error .InvalidDigit := by
  induction l generalizing a with
  | nil =>
    simp [stdDigits, allDigits, decimal, hahi]
  | cons b bs ih =>
    by_cases hd : isDigit b
    · have hd0 := digit_sub48_nonneg hd
      have hd9 := digit_sub48_le9 hd
      have hval : a * 10 ^ (b :: bs).length + (decimal (b :: bs) : ℤ) =
          (a * 10 + ((b.val : ℤ) - 48)) * 10 ^ bs.length + (decimal bs : ℤ) := by
        rw [decimal_cons, List.length_cons]
        have h48 : ((b.val - 48 : ℕ) : ℤ) = (b.val : ℤ) - 48 := by
          have := hd.1; omega
        push_cast [h48]
        ring
      rw [hval]
      have hall : allDigits (b :: bs) ↔ allDigits bs := by simp [allDigits, hd]
      simp only [hall]
      rw [stdDigits_cons lo hi a b bs hd]
      have hlo' : lo ≤ a * 10 + ((b.val : ℤ) - 48) := by omega
      rcases bs with _ | ⟨c, cs⟩
      · -- last digit: in range or overflow, both sides agree
        by_cases hhi : a * 10 + ((b.val : ℤ) - 48) ≤ hi
        · simp [stdDigits, allDigits, decimal, hlo', hhi]
        · simp [allDigits, decimal, hhi]
      · -- more digits: the new accumulator fits, by `hb` at `k = 1`
        have h1 := hb 1 (by simp)
        have ha'hi : a * 10 + ((b.val : ℤ) - 48) ≤ hi := by omega
        simp only [hlo', ha'hi, and_self, ite_true]
        apply ih _ (by omega) ha'hi
        intro k hk
        have h2 := hb (k + 1) (by simp at hk ⊢; omega)
        have hp : (0 : ℤ) ≤ 10 ^ k := by positivity
        have hstep : ((b.val : ℤ) - 48 + 1) * 10 ^ k ≤ 10 * 10 ^ k := by nlinarith
        rw [pow_succ] at h2
        nlinarith
    · rw [stdDigits_nonDigit lo hi false a b bs hd]
      simp [allDigits, hd]

/-- An accumulator already past `hi`, with a digit still to read: never `ok`. -/
theorem stdDigits_err_of_big (lo hi a : ℤ) (l : List U8) (ha : 0 ≤ a)
    (hbig : hi < a * 10 ^ l.length) (hne : l ≠ []) : ∃ k, stdDigits lo hi false a l = .error k := by
  rcases h : stdDigits lo hi false a l with k | v
  · exact ⟨k, rfl⟩
  · exfalso
    obtain ⟨h1, h2⟩ := stdDigits_ok_bounds lo hi a l v ha h
    have := h2 hne
    omega

/-- The positive fold only ever reports a bad digit or a positive overflow. -/
theorem stdDigits_pos_err_kinds (lo hi a : ℤ) (l : List U8) (k : Kind)
    (h : stdDigits lo hi false a l = .error k) : k = .PosOverflow ∨ k = .InvalidDigit := by
  induction l generalizing a with
  | nil => simp [stdDigits] at h
  | cons b bs ih =>
    by_cases hb : isDigit b
    · rw [stdDigits_cons lo hi a b bs hb] at h
      split_ifs at h with hr
      · exact ih _ h
      · simp at h; exact Or.inl h.symm
    · rw [stdDigits_nonDigit lo hi false a b bs hb] at h
      simp at h; exact Or.inr h.symm

/-- Leading `'0'`s do not matter to the fold from zero. -/
theorem stdDigits_dropZeros (lo hi : ℤ) (l : List U8) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    stdDigits lo hi false 0 l = stdDigits lo hi false 0 (l.dropWhile fun b => decide (b = 48#u8)) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = 48#u8
    · subst hb
      rw [stdDigits_cons_zero lo hi bs hlo hhi, ih]
      simp
    · simp [hb]

/-- All zeros: the number is zero. -/
theorem stdDigits_zeros (lo hi : ℤ) (l : List U8) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (h : l.dropWhile (fun b => decide (b = 48#u8)) = []) : stdDigits lo hi false 0 l = .ok 0 := by
  rw [stdDigits_dropZeros lo hi l hlo hhi, h]; rfl

/-- `(hi + 1) / 10^(c-1)`, the first significant digit, is at most 9 when its weight fits. -/
theorem fs_le_9 (hi : ℤ) (c : ℕ) (hc : hi < 10 ^ c) (hc1 : 1 ≤ c)
    (hmul : ((hi + 1) / 10 ^ (c - 1)) * 10 ^ (c - 1) ≤ hi) : (hi + 1) / 10 ^ (c - 1) ≤ 9 := by
  have hp : (0 : ℤ) < 10 ^ (c - 1) := by positivity
  have hc' : (10 : ℤ) ^ c = 10 * 10 ^ (c - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hc'] at hc
  by_contra hlt
  simp only [not_le] at hlt
  have : 10 * 10 ^ (c - 1) ≤ ((hi + 1) / 10 ^ (c - 1)) * 10 ^ (c - 1) := by nlinarith
  omega

/-- The floor bound: `hi + 1 < (fs + 1) · 10^(c-1)`. -/
theorem fs_floor (hi : ℤ) (c : ℕ) : hi + 1 < ((hi + 1) / 10 ^ (c - 1) + 1) * 10 ^ (c - 1) := by
  have hp : (0 : ℤ) < 10 ^ (c - 1) := by positivity
  exact Int.lt_ediv_add_one_mul_self (hi + 1) hp

end atoi_radix10
