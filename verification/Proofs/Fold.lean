import Proofs.DigitTest

/-!
One SWAR fold step, for any lane width. A word of `2n` lanes `g0, g1, …` (each a group of
digits) becomes a word of `n` lanes twice as wide holding `c·g0 + g1, c·g2 + g3, …`:

  `((x & odd_mask) >> w) + (x & even_mask) * c`

where the masks keep the odd, resp. even, lanes (`m` bits of each). `fold_step` is that
identity on `lanes`; the parsers apply it with `w = 8, m = 0xf, c = 10`, then
`w = 16, m = 0xff, c = 100`, then `w = 32, m = 0xffff, c = 10000`.
-/

open Aeneas Aeneas.Std

namespace atoi_radix10

/-- `[m, 0, m, 0, …]`, `2n` lanes: the even lanes. -/
def evenMask (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => m :: 0 :: evenMask m n

/-- `[0, m, 0, m, …]`, `2n` lanes: the odd lanes. -/
def oddMask (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => 0 :: m :: oddMask m n

/-- `[c·g0 + g1, c·g2 + g3, …]`. -/
def pairFold (c : ℕ) : List ℕ → List ℕ
  | g0 :: g1 :: rest => (c * g0 + g1) :: pairFold c rest
  | _ => []

/-- `[f0, 0, f1, 0, …]`: `n` lanes spread over `2n`. -/
def spread : List ℕ → List ℕ
  | f :: rest => f :: 0 :: spread rest
  | [] => []

theorem evenMask_length (m n : ℕ) : (evenMask m n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [evenMask, ih]; ring

theorem oddMask_length (m n : ℕ) : (oddMask m n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [oddMask, ih]; ring

theorem evenMask_mem (m n : ℕ) : ∀ x ∈ evenMask m n, x = m ∨ x = 0 := by
  induction n with
  | zero => simp [evenMask]
  | succ n ih => intro x hx; simp only [evenMask, List.mem_cons] at hx; rcases hx with rfl | rfl | hx
                 · exact Or.inl rfl
                 · exact Or.inr rfl
                 · exact ih x hx

theorem oddMask_mem (m n : ℕ) : ∀ x ∈ oddMask m n, x = m ∨ x = 0 := by
  induction n with
  | zero => simp [oddMask]
  | succ n ih => intro x hx; simp only [oddMask, List.mem_cons] at hx; rcases hx with rfl | rfl | hx
                 · exact Or.inr rfl
                 · exact Or.inl rfl
                 · exact ih x hx

/-- Spread lanes regroup into lanes twice as wide. -/
theorem lanes_spread (w : ℕ) (fs : List ℕ) : lanes w (spread fs) = lanes (2 * w) fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [spread, lanes_pairs, ih, lanes_cons]

/-- The fold, lane by lane: masking, shifting, scaling and adding `2n` lanes. -/
theorem fold_lists (m c n : ℕ) (gs : List ℕ) (hlen : gs.length = 2 * n) :
    List.zipWith (· + ·)
        ((List.zipWith (· &&& ·) gs (oddMask m n)).drop 1 ++ [0])
        ((List.zipWith (· &&& ·) gs (evenMask m n)).map (c * ·)) =
      spread (pairFold c (gs.map (· &&& m))) := by
  induction n generalizing gs with
  | zero =>
    cases gs with
    | nil => rfl
    | cons => simp at hlen
  | succ n ih =>
    match gs, hlen with
    | g0 :: g1 :: rest, hlen =>
      have hrest : rest.length = 2 * n := by simp at hlen; omega
      simp only [oddMask, evenMask, List.zipWith_cons_cons, List.drop_succ_cons, List.drop_zero,
        List.map_cons, List.cons_append, pairFold, spread, Nat.and_zero, Nat.mul_zero]
      rw [Nat.add_comm (g1 &&& m)]
      congr 1
      cases rest with
      | nil =>
        cases n with
        | zero => rfl
        | succ n => simp at hrest
      | cons g2 rest' =>
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hrest; omega⟩
        have ih' := ih (g2 :: rest') hrest
        simp only [oddMask, evenMask, List.zipWith_cons_cons, List.drop_succ_cons, List.drop_zero,
          List.map_cons, List.cons_append, Nat.and_zero, Nat.zero_add] at ih' ⊢
        rw [ih']

/-- Masking keeps lanes small. -/
theorem zipWith_and_lt (w : ℕ) (gs ms : List ℕ) (hg : ∀ g ∈ gs, g < 2 ^ w) :
    ∀ x ∈ List.zipWith (· &&& ·) gs ms, x < 2 ^ w := by
  induction gs generalizing ms with
  | nil => simp
  | cons g gs ih =>
    cases ms with
    | nil => simp
    | cons m ms =>
      simp only [List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨lt_of_le_of_lt Nat.and_le_left (hg g (by simp)), ih ms (fun g hg' => hg g (by simp [hg']))⟩

/-- One fold step on the word: the odd lanes shifted down, plus the even lanes scaled. The
lanes must fit (`< 2^w`), and so must the mask. -/
theorem fold_step (w m c n : ℕ) (hn : 0 < n) (gs : List ℕ) (hlen : gs.length = 2 * n)
    (hg : ∀ g ∈ gs, g < 2 ^ w) (hm : m < 2 ^ w) :
    (lanes w gs &&& lanes w (oddMask m n)) >>> w + (lanes w gs &&& lanes w (evenMask m n)) * c =
      lanes (2 * w) (pairFold c (gs.map (· &&& m))) := by
  have hodd : ∀ x ∈ oddMask m n, x < 2 ^ w := fun x hx => by
    rcases oddMask_mem m n x hx with rfl | rfl
    · exact hm
    · positivity
  have heven : ∀ x ∈ evenMask m n, x < 2 ^ w := fun x hx => by
    rcases evenMask_mem m n x hx with rfl | rfl
    · exact hm
    · positivity
  have hlens : ((List.zipWith (· &&& ·) gs (oddMask m n)).drop 1 ++ [0]).length =
      ((List.zipWith (· &&& ·) gs (evenMask m n)).map (c * ·)).length := by
    simp [List.length_zipWith, hlen, oddMask_length, evenMask_length]; omega
  rw [lanes_and w gs (oddMask m n) hg hodd (by rw [hlen, oddMask_length]),
    lanes_and w gs (evenMask m n) hg heven (by rw [hlen, evenMask_length]),
    Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ w = (2 ^ w) ^ 1 by norm_num,
    lanes_div w 1 _ (zipWith_and_lt w gs _ hg), ← lanes_snoc_zero, Nat.mul_comm, lanes_mul,
    lanes_add w _ _ hlens, fold_lists m c n gs hlen, lanes_spread]

end atoi_radix10
