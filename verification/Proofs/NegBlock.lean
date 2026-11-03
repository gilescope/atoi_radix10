import Proofs.Block

/-!
The negative path of `parse` (`src/parse.rs` lines 365-526): after a `-`, the same pre-pass and
SWAR block as the positive path, subtracting instead of adding, against the negative fold
`stdDigits lo hi true`. Its early `return`s were lifted out of two nested loops, so a result
comes back in one of 22 `Option` slots; `SlotsOK` says one slot is set and whatever is set is
right.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The reference for the bytes after a `-`: a lone sign is `InvalidDigit` (core's rule), else the
negative fold. -/
def negRef (lo hi : ℤ) (D0 : List U8) : Except Kind ℤ :=
  if D0 = [] then .error .InvalidDigit else stdDigits lo hi true 0 D0

theorem negRef_of_ne (lo hi : ℤ) {D0 : List U8} (h : D0 ≠ []) :
    negRef lo hi D0 = stdDigits lo hi true 0 D0 := by
  simp [negRef, h]

/-- The result of the whole negative path, against the reference. -/
def NegResult {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) :
    core.result.Result T ParseIntErrorPublic → Prop
  | .Ok t => negRef lo hi D0 = .ok (toInt t)
  | .Err e => ∃ k, negRef lo hi D0 = .error k ∧ kindLike e.kind k

/-- Some slot is set, and every set slot holds a right answer. -/
def SlotsOK {α : Type} (P : α → Prop) (l : List (Option α)) : Prop :=
  (∃ r, some r ∈ l) ∧ ∀ r, some r ∈ l → P r

theorem SlotsOK_of_mem {α : Type} {P : α → Prop} {l : List (Option α)} {r : α} (hm : some r ∈ l)
    (hr : P r) (hall : ∀ r', some r' ∈ l → r' = r) : SlotsOK P l :=
  ⟨⟨r, hm⟩, fun r' h => (hall r' h) ▸ hr⟩

/-- What the negative pre-pass established: `a ≤ 0` accounts for the bytes consumed (the digit
set aside, negated), no proper prefix can overflow downwards, and `checked` holds that digit
with its positive weight. -/
structure NegHandover {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 D : List U8)
    (checked : Option (U8 × T)) : Prop where
  len_pos : 0 < D.length
  len_lt : D.length < c
  acc : ∃ a : ℤ, a ≤ 0 ∧ lo ≤ a ∧ stdDigits lo hi true 0 D0 = stdDigits lo hi true a D ∧
    (∀ k, k < D.length → lo ≤ a * 10 ^ k - (10 ^ k - 1)) ∧
    (checked = none → a = 0) ∧
    (∀ d t, checked = some (d, t) →
      a = -(d.val : ℤ) ∧ toInt t = (d.val : ℤ) * 10 ^ D.length ∧ D.length + 1 = c)
  d0_ne : D0 ≠ []

/-- Inside the negative block: `k` bytes consumed, all digits, `res` their value negated at the
weight of what remains. -/
def NegBlockInv {T : Type} (toInt : T → ℤ) (D : List U8) (s : Slice U8) (res : T) : Prop :=
  ∃ k, k < D.length ∧ s.val = D.drop k ∧ allDigits (D.take k) ∧
    toInt res = -((decimal (D.take k) : ℤ) * 10 ^ (D.length - k))

/-- One chunk of `N` digits, read as `v`, subtracted: the negative counterpart of `chunk_step`. -/
theorem chunk_step_neg {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ} {lo hi : ℤ}
    {c : ℕ} (hF : Faithful inst toInt lo hi c) (hlo : lo < 0) (D : List U8) (hD : D.length < c)
    (k N : ℕ) (hkN : k + N ≤ D.length) (hk : allDigits (D.take k))
    (hN : allDigits ((D.drop k).take N)) (v : ℤ) (hv : v = (decimal ((D.drop k).take N) : ℤ)) :
    allDigits (D.take (k + N)) ∧
    0 ≤ v ∧ v ≤ hi ∧
    InRange lo hi (10 ^ (D.length - (k + N)) * v) ∧
    InRange lo hi (-((decimal (D.take k) : ℤ) * 10 ^ (D.length - k)) - 10 ^ (D.length - (k + N)) * v) ∧
    -((decimal (D.take k) : ℤ) * 10 ^ (D.length - k)) - 10 ^ (D.length - (k + N)) * v =
      -((decimal (D.take (k + N)) : ℤ) * 10 ^ (D.length - (k + N))) ∧
    (k + N = D.length → -((decimal (D.take k) : ℤ) * 10 ^ (D.length - k)) - v = -(decimal D : ℤ)) := by
  obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hres, hfull⟩ := chunk_step hF D hD k N hkN hk hN v hv
  have hsigned := hF.signed hlo
  have hY : (0 : ℤ) ≤ 10 ^ (D.length - (k + N)) * v := mul_nonneg (by positivity) hv0
  refine ⟨hall', hv0, hvhi, hmr, ⟨?_, ?_⟩, by linarith, fun h => by have := hfull h; linarith⟩
  · have := har.2; linarith
  · have := hF.hi_pos; linarith

/-! ### The final answer -/

theorem final_neg_unchecked {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (hlo : lo < 0) {D0 D : List U8}
    (hH : NegHandover toInt lo hi c D0 D none) (hall : allDigits D) (resF : T)
    (hres : toInt resF = -(decimal D : ℤ)) : NegResult toInt lo hi D0 (.Ok resF) := by
  have hne := hH.d0_ne
  obtain ⟨hlen, hlt, ⟨a, ha0, halo, hfold, hb, hn, _⟩, _⟩ := hH
  have ha : a = 0 := hn rfl
  subst ha
  show negRef lo hi D0 = .ok (toInt resF)
  rw [negRef_of_ne lo hi hne, hfold, stdDigits_neg_closed lo hi 0 D (le_refl 0) (le_of_lt hF.hi_pos) halo hb]
  obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D hall hlt
  have hsigned : lo ≤ -(decimal D : ℤ) := by have := hF.signed hlo; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
  have h2 : lo ≤ 0 * 10 ^ D.length - (decimal D : ℤ) := by simpa using hsigned
  rw [ite_eq_left_of_eq_true _ _ (eq_true h2), hres]
  simp

/-- With a digit set aside: `res - chk_t`, checked, or `MIN` straight away when `res = TAIL` and the
digit is the first significant one (the same value). -/
theorem final_neg_checked_value {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8} {d : U8} {ct : T}
    (hH : NegHandover toInt lo hi c D0 D (some (d, ct))) (hall : allDigits D) (resF : T)
    (hres : toInt resF = -(decimal D : ℤ)) :
    stdDigits lo hi true 0 D0 =
      (if lo ≤ toInt resF - toInt ct then .ok (toInt resF - toInt ct) else .error .NegOverflow) := by
  obtain ⟨hlen, hlt, ⟨a, ha0, halo, hfold, hb, _, hs⟩, _⟩ := hH
  obtain ⟨ha, hct, _⟩ := hs d ct rfl
  have hval : toInt resF - toInt ct = a * 10 ^ D.length - (decimal D : ℤ) := by
    rw [hres, hct, ha]; ring
  rw [hval, hfold, stdDigits_neg_closed lo hi a D ha0 (le_of_lt hF.hi_pos) halo hb,
    ite_eq_left_of_eq_true _ _ (eq_true hall)]

theorem final_neg_checked {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8} {d : U8} {ct : T}
    (hH : NegHandover toInt lo hi c D0 D (some (d, ct))) (hall : allDigits D) (resF : T)
    (hres : toInt resF = -(decimal D : ℤ)) (o : Option T)
    (ho : CheckedIs toInt lo hi (toInt resF - toInt ct) o) :
    core.option.Option.ok_or o ({ kind := .NegOverflow } : ParseIntErrorPublic)
      ⦃ r => NegResult toInt lo hi D0 r ⦄ := by
  have hv := final_neg_checked_value hF hH hall resF hres
  have hne := hH.d0_ne
  rcases o with _ | z
  · have ho' : ¬ InRange lo hi (toInt resF - toInt ct) := ho
    simp only [InRange, not_and, not_le] at ho'
    have hneg : toInt resF - toInt ct < lo := by
      by_contra h
      simp only [not_lt] at h
      have hhi' := ho' h
      obtain ⟨hlen, hlt, ⟨a, ha0, halo, hfold, hb, _, hs⟩, _⟩ := hH
      obtain ⟨ha, hct, _⟩ := hs d ct rfl
      have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
      have hq : (0 : ℤ) ≤ 10 ^ D.length := by positivity
      have hd0 : (0 : ℤ) ≤ (d.val : ℤ) := by omega
      have hm := mul_nonneg hd0 hq
      rw [hres, hct] at hhi'
      have := hF.hi_pos
      omega
    rw [core.option.Option.ok_or_none, WP.spec_ok]
    show ∃ k, negRef lo hi D0 = .error k ∧ kindLike .NegOverflow k
    refine ⟨.NegOverflow, ?_, Or.inl rfl⟩
    rw [negRef_of_ne lo hi hne, hv, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hneg))]
  · have ho' : InRange lo hi (toInt resF - toInt ct) ∧ toInt z = toInt resF - toInt ct := ho
    obtain ⟨⟨hle, _⟩, hz⟩ := ho'
    rw [core.option.Option.ok_or_some, WP.spec_ok]
    show negRef lo hi D0 = .ok (toInt z)
    rw [negRef_of_ne lo hi hne, hv, ite_eq_left_of_eq_true _ _ (eq_true hle), hz]

/-- A bad digit in the bytes: the reference says `InvalidDigit`. -/
theorem final_neg_invalid {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {checked : Option (U8 × T)} (hH : NegHandover toInt lo hi c D0 D checked) (hnot : ¬ allDigits D)
    (e : ParseIntErrorPublic) (he : e.kind = .InvalidDigit) : NegResult toInt lo hi D0 (.Err e) := by
  have hne := hH.d0_ne
  obtain ⟨_, _, ⟨a, ha0, halo, hfold, hb, _, _⟩, _⟩ := hH
  refine ⟨.InvalidDigit, ?_, Or.inl he⟩
  have hc := stdDigits_neg_closed lo hi a D ha0 (le_of_lt hF.hi_pos) halo hb
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)] at hc
  rw [negRef_of_ne lo hi hne]
  exact hfold.trans hc

/-- The shortcut: `res = TAIL` with the first significant digit set aside is `MIN`. -/
theorem final_neg_tail {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8} {d : U8}
    {ct : T} (hH : NegHandover toInt lo hi c D0 D (some (d, ct))) (hall : allDigits D) (resF : T)
    (hres : toInt resF = -(decimal D : ℤ)) (tl mn : T)
    (htl : toInt tl = lo + ((hi + 1) / 10 ^ (c - 1)) * 10 ^ (c - 1)) (hmn : toInt mn = lo)
    (heq : toInt resF = toInt tl) (hfs : (d.val : ℤ) = (hi + 1) / 10 ^ (c - 1)) :
    NegResult toInt lo hi D0 (.Ok mn) := by
  have hv := final_neg_checked_value hF hH hall resF hres
  have hne := hH.d0_ne
  obtain ⟨hlen, hlt, ⟨a, ha0, halo, hfold, hb, _, hs⟩, _⟩ := hH
  obtain ⟨ha, hct, hDc'⟩ := hs d ct rfl
  have hDc : D.length = c - 1 := by omega
  show negRef lo hi D0 = .ok (toInt mn)
  rw [negRef_of_ne lo hi hne, hv, hmn]
  have : toInt resF - toInt ct = lo := by rw [heq, htl, hct, hfs, hDc]; ring
  rw [this]; simp

end atoi_radix10
