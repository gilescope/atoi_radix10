import Proofs.Bytes

/-!
Words as lanes. `lanes w xs` is the number whose `w`-bit lanes hold `xs`, least significant
first; the SWAR parsers' masks, shifts, additions and small multiplications all act lane by
lane, and these lemmas say so. Entries may exceed a lane (after a multiplication) as long as the
lanes above them are zero: `lanes_pairs` then regroups into twice-as-wide lanes.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- The number whose `w`-bit lanes hold `xs`, least significant first. -/
def lanes (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ w * lanes w xs

@[simp] theorem lanes_nil (w : ℕ) : lanes w [] = 0 := rfl

@[simp] theorem lanes_cons (w x : ℕ) (xs : List ℕ) : lanes w (x :: xs) = x + 2 ^ w * lanes w xs :=
  rfl

theorem leBytes_eq_lanes (bs : List U8) : leBytes bs = lanes 8 (bs.map UScalar.val) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [leBytes, ih]

theorem lanes_lt (w : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < 2 ^ w) :
    lanes w xs < (2 ^ w) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [lanes_cons, List.length_cons, pow_succ]
    have h2 : 0 < 2 ^ w := by positivity
    nlinarith

theorem lanes_eq_zero (w : ℕ) (xs : List ℕ) : lanes w xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h2 : 0 < 2 ^ w := by positivity
    simp only [lanes_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h; have hx : x = 0 := by omega
      have : lanes w xs = 0 := by nlinarith
      exact ⟨hx, ih.mp this⟩
    · rintro ⟨hx, hxs⟩; rw [hx, ih.mpr hxs]; simp

/-- A bitwise operation on two words acts lane by lane. -/
theorem lanes_bitwise (f : Bool → Bool → Bool) (hf : f false false = false) (w : ℕ)
    (xs ys : List ℕ) (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (hl : xs.length = ys.length) :
    Nat.bitwise f (lanes w xs) (lanes w ys) = lanes w (List.zipWith (Nat.bitwise f) xs ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [lanes_cons, List.zipWith_cons_cons]
      rw [add_comm x, add_comm y,
        Nat.bitwise_split f hf (hx x (by simp)) (hy y (by simp)),
        ih ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz]))
          (by simpa using hl)]
      ring

theorem lanes_and (w : ℕ) (xs ys : List ℕ) (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (hl : xs.length = ys.length) :
    lanes w xs &&& lanes w ys = lanes w (List.zipWith (· &&& ·) xs ys) :=
  lanes_bitwise and rfl w xs ys hx hy hl

theorem lanes_or (w : ℕ) (xs ys : List ℕ) (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (hl : xs.length = ys.length) :
    lanes w xs ||| lanes w ys = lanes w (List.zipWith (· ||| ·) xs ys) :=
  lanes_bitwise or rfl w xs ys hx hy hl

theorem lanes_xor (w : ℕ) (xs ys : List ℕ) (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (hl : xs.length = ys.length) :
    lanes w xs ^^^ lanes w ys = lanes w (List.zipWith (· ^^^ ·) xs ys) :=
  lanes_bitwise bne rfl w xs ys hx hy hl

/-- Addition is lane by lane, carries included in the entries. -/
theorem lanes_add (w : ℕ) (xs ys : List ℕ) (hl : xs.length = ys.length) :
    lanes w xs + lanes w ys = lanes w (List.zipWith (· + ·) xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => simp | cons => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys => simp only [lanes_cons, List.zipWith_cons_cons]; rw [← ih ys (by simpa using hl)]; ring

/-- Multiplying a word multiplies every entry. -/
theorem lanes_mul (w k : ℕ) (xs : List ℕ) : k * lanes w xs = lanes w (xs.map (k * ·)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [lanes_cons, List.map_cons]; rw [← ih]; ring

/-- Dropping the low lanes: a shift right by whole lanes. -/
theorem lanes_div (w n : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < 2 ^ w) :
    lanes w xs / (2 ^ w) ^ n = lanes w (xs.drop n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      have hx := h x (by simp)
      have h2 : 0 < 2 ^ w := by positivity
      simp only [lanes_cons, List.drop_succ_cons, pow_succ]
      rw [← ih xs (fun y hy => h y (by simp [hy])), Nat.mul_comm ((2 ^ w) ^ n) (2 ^ w),
        ← Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.mul_comm (2 ^ w) (lanes w xs), Nat.add_mul_div_right _ _ h2, Nat.div_eq_of_lt hx,
        Nat.zero_add]

/-- Keeping the low lanes: a cast to a narrower word. -/
theorem lanes_mod (w n : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < 2 ^ w) :
    lanes w xs % (2 ^ w) ^ n = lanes w (xs.take n) := by
  have hdm := Nat.div_add_mod (lanes w xs) ((2 ^ w) ^ n)
  rw [lanes_div w n xs h] at hdm
  have hsplit : lanes w xs = lanes w (xs.take n) + (2 ^ w) ^ n * lanes w (xs.drop n) := by
    conv_lhs => rw [← List.take_append_drop n xs]
    clear hdm
    induction n generalizing xs with
    | zero => simp
    | succ n ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, lanes_cons, pow_succ]
        rw [ih xs (fun y hy => h y (by simp [hy]))]; ring
  have hlt : lanes w (xs.take n) < (2 ^ w) ^ n := by
    have := lanes_lt w (xs.take n) (fun y hy => h y (List.mem_of_mem_take hy))
    calc lanes w (xs.take n) < (2 ^ w) ^ (xs.take n).length := this
      _ ≤ (2 ^ w) ^ n := Nat.pow_le_pow_right (by positivity) (by simp)
  omega

/-- Lanes whose odd entries are zero regroup into lanes twice as wide. -/
theorem lanes_pairs (w x : ℕ) (xs : List ℕ) :
    lanes w (x :: 0 :: xs) = x + 2 ^ (2 * w) * lanes w xs := by
  simp only [lanes_cons]; rw [show 2 ^ (2 * w) = 2 ^ w * 2 ^ w by rw [two_mul, pow_add]]; ring

end atoi_radix10
