import Proofs.Lanes

/-!
The SWAR digit test, for any number of bytes. With `c = b ^ 0x30` in every lane, the parsers
check `(c & 0xf0..) = 0` and `((c +wrap 0x76..) & 0x80..) = 0`: the first says every lane is below
16, and then the second, which cannot carry between lanes, says every lane is at most 9. Together
they say every byte `b` was an ASCII digit, and `c` is its value.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- Lanes of the same constant. -/
theorem mem_replicate_eq {n k x : ℕ} (hx : x ∈ List.replicate n k) : x = k :=
  (List.mem_replicate.mp hx).2

theorem lanes_snoc_zero (w : ℕ) (xs : List ℕ) : lanes w (xs ++ [0]) = lanes w xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Every lane of `c & 0xf0..` is zero exactly when every lane is below 16. -/
theorem lanes_hi_zero (cs : List ℕ) (hc : ∀ c ∈ cs, c < 2 ^ 8) :
    (∀ x ∈ List.zipWith (· &&& ·) cs (List.replicate cs.length 240), x = 0) ↔
      ∀ c ∈ cs, c < 16 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.mem_cons,
      forall_eq_or_imp]
    have hc' := hc c (by simp)
    rw [ih (fun x hx => hc x (by simp [hx]))]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨byte_hi_zero c hc' h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨byte_lt16_hi_zero c h0, h⟩

/-- With every lane below 16, every lane of `(c + 0x76..) & 0x80..` is zero exactly when every
lane is at most 9. -/
theorem lanes_lo_zero (cs : List ℕ) (hc : ∀ c ∈ cs, c < 16) :
    (∀ x ∈ List.zipWith (· &&& ·) (List.zipWith (· + ·) cs (List.replicate cs.length 118))
        (List.replicate cs.length 128), x = 0) ↔
      ∀ c ∈ cs, c ≤ 9 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.mem_cons,
      forall_eq_or_imp]
    have hc' := hc c (by simp)
    rw [ih (fun x hx => hc x (by simp [hx])), byte_lo_test c hc']

/-- Adding a constant to every lane keeps the lanes small when the sums are. -/
theorem zipWith_add_replicate_lt (cs : List ℕ) (k : ℕ) (h : ∀ c ∈ cs, c + k < 2 ^ 8) :
    ∀ x ∈ List.zipWith (· + ·) cs (List.replicate cs.length k), x < 2 ^ 8 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.mem_cons,
      forall_eq_or_imp]
    exact ⟨h c (by simp), ih (fun c hc => h c (by simp [hc]))⟩

/-- The test as the parsers compute it, on the word `lanes 8 cs`: both halves are zero exactly
when every lane is at most 9. -/
theorem digit_test (cs : List ℕ) (hc : ∀ c ∈ cs, c < 2 ^ 8) :
    (lanes 8 cs &&& lanes 8 (List.replicate cs.length 240) = 0 ∧
      ((lanes 8 cs + lanes 8 (List.replicate cs.length 118)) % (2 ^ 8) ^ cs.length) &&&
          lanes 8 (List.replicate cs.length 128) = 0) ↔
      ∀ c ∈ cs, c ≤ 9 := by
  have hrep : ∀ k : ℕ, k < 2 ^ 8 → ∀ x ∈ List.replicate cs.length k, x < 2 ^ 8 :=
    fun k hk x hx => (mem_replicate_eq hx) ▸ hk
  have hlen : ∀ k : ℕ, cs.length = (List.replicate cs.length k).length := fun k => by simp
  rw [lanes_and 8 cs _ hc (hrep 240 (by norm_num)) (hlen 240), lanes_eq_zero, lanes_hi_zero cs hc]
  -- once every lane is below 16, the addition neither carries nor wraps
  have hsum : (∀ c ∈ cs, c < 16) →
      ((lanes 8 cs + lanes 8 (List.replicate cs.length 118)) % (2 ^ 8) ^ cs.length) &&&
          lanes 8 (List.replicate cs.length 128) =
        lanes 8 (List.zipWith (· &&& ·)
          (List.zipWith (· + ·) cs (List.replicate cs.length 118))
          (List.replicate cs.length 128)) := by
    intro hlt
    have hadd := lanes_add 8 cs (List.replicate cs.length 118) (hlen 118)
    have hbound := zipWith_add_replicate_lt cs 118 (fun c hc => by have := hlt c hc; omega)
    have hlt' := lanes_lt 8 _ hbound
    rw [show (List.zipWith (· + ·) cs (List.replicate cs.length 118)).length = cs.length by simp]
      at hlt'
    rw [hadd, Nat.mod_eq_of_lt hlt', lanes_and 8 _ _ hbound (hrep 128 (by norm_num)) (by simp)]
  constructor
  · rintro ⟨hlt, h⟩
    rw [hsum hlt, lanes_eq_zero, lanes_lo_zero cs hlt] at h
    exact h
  · intro h
    have hlt : ∀ c ∈ cs, c < 16 := fun c hc => by have := h c hc; omega
    refine ⟨hlt, ?_⟩
    rw [hsum hlt, lanes_eq_zero, lanes_lo_zero cs hlt]
    exact h

end atoi_radix10
