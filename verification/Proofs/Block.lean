import Proofs.ParseLoops
import Proofs.Swar32

/-!
The SWAR block of the positive path (`src/parse.rs` lines 204-327, `parse_inner_loop2`): the
definitions and arithmetic the block proof runs on. The block consumes the bytes `D` the
pre-pass handed over, chunk by chunk, keeping `res` equal to the value of the consumed digits
at the weight of what remains; a non-digit anywhere is `InvalidDigit`; at the end the digit set
aside by the pre-pass (if any) is added with an overflow check.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- `load::misaligned` answers, whatever it answers. -/
@[step]
theorem load.misaligned_spec (s : Slice U8) (bit : Usize) :
    load.misaligned s bit ⦃ _ => True ⦄ := by
  simp [load.misaligned, WP.spec_ok]

/-- Inside the block over the bytes `D`: `k` of them consumed, all digits, and `res` is their
value at the weight of the `|D| - k` that remain, which `s` holds. -/
def BlockInv {T : Type} (toInt : T → ℤ) (D : List U8) (s : Slice U8) (res : T) : Prop :=
  ∃ k, k < D.length ∧ s.val = D.drop k ∧ allDigits (D.take k) ∧
    toInt res = (decimal (D.take k) : ℤ) * 10 ^ (D.length - k)

/-- What the pre-pass established about `checked` and the bytes `D` it handed over. -/
structure Handover {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 D : List U8)
    (checked : Option (U8 × T)) : Prop where
  len_pos : 0 < D.length
  len_lt : D.length < c
  acc : ∃ a : ℤ, 0 ≤ a ∧ a ≤ hi ∧ stdDigits lo hi false 0 D0 = stdDigits lo hi false a D ∧
    (∀ k, k < D.length → a * 10 ^ k + (10 ^ k - 1) ≤ hi) ∧
    (checked = none → a = 0) ∧ (∀ d t, checked = some (d, t) → toInt t = a * 10 ^ D.length)

theorem Handover.of_pre {T : Type} {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} {D0 : List U8}
    {s : Slice U8} {checked : Option (U8 × T)} {val1 : U8}
    (h : PreInv toInt lo hi c D0 s checked val1) (hlt : s.val.length < c) :
    Handover toInt lo hi c D0 s.val checked := by
  obtain ⟨hlen, _, a, ha0, hahi, hfold, hb, hn, hs⟩ := h
  exact ⟨hlen, hlt, a, ha0, hahi, hfold, fun k hk => hb k hk (by omega), hn, fun d t hdt => (hs d t hdt).1⟩

/-! ### Chunk arithmetic -/

theorem take_add_drop (D : List U8) (k N : ℕ) :
    D.take (k + N) = D.take k ++ (D.drop k).take N := by
  rw [List.take_add]

theorem allDigits_append {xs ys : List U8} (hx : allDigits xs) (hy : allDigits ys) :
    allDigits (xs ++ ys) := by
  intro b hb; rw [List.mem_append] at hb; rcases hb with h | h
  · exact hx b h
  · exact hy b h

theorem allDigits_take_of_take_drop {D : List U8} {k N : ℕ} (hk : allDigits (D.take k))
    (hN : allDigits ((D.drop k).take N)) : allDigits (D.take (k + N)) := by
  rw [take_add_drop]; exact allDigits_append hk hN

theorem decimal_take_add (D : List U8) (k N : ℕ) (h : k + N ≤ D.length) :
    (decimal (D.take (k + N)) : ℤ) =
      (decimal (D.take k) : ℤ) * 10 ^ N + (decimal ((D.drop k).take N) : ℤ) := by
  rw [take_add_drop, decimal_append]
  have hlen : ((D.drop k).take N).length = N := by simp; omega
  rw [hlen]; push_cast; ring

/-- The value of `j` digits is below `10^j`, hence at most `hi` for `j < c`. -/
theorem decimal_take_lt_hi {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (l : List U8) (hall : allDigits l)
    (hl : l.length < c) : (decimal l : ℤ) < 10 ^ l.length ∧ (decimal l : ℤ) ≤ hi := by
  have h1 : decimal l < 10 ^ l.length := decimal_lt l hall
  have h2 : (10 : ℤ) ^ l.length ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 := hF.hi_ge
  constructor
  · exact_mod_cast h1
  · have : (decimal l : ℤ) < 10 ^ l.length := by exact_mod_cast h1
    omega

/-- One chunk of `N` digits, read as `v`, folded in: the invariant moves on by `N`, or the
block is complete when nothing remains. All intermediate values stay below `10^|D|`. -/
theorem chunk_step {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ} {lo hi : ℤ}
    {c : ℕ} (hF : Faithful inst toInt lo hi c) (D : List U8) (hD : D.length < c)
    (k N : ℕ) (hkN : k + N ≤ D.length) (hk : allDigits (D.take k))
    (hN : allDigits ((D.drop k).take N)) (v : ℤ) (hv : v = (decimal ((D.drop k).take N) : ℤ)) :
    allDigits (D.take (k + N)) ∧
    0 ≤ (decimal (D.take k) : ℤ) * 10 ^ (D.length - k) ∧ 0 ≤ v ∧ v ≤ hi ∧
    InRange lo hi (10 ^ (D.length - (k + N)) * v) ∧
    InRange lo hi ((decimal (D.take k) : ℤ) * 10 ^ (D.length - k) + 10 ^ (D.length - (k + N)) * v) ∧
    (decimal (D.take k) : ℤ) * 10 ^ (D.length - k) + 10 ^ (D.length - (k + N)) * v =
      (decimal (D.take (k + N)) : ℤ) * 10 ^ (D.length - (k + N)) ∧
    (k + N = D.length → (decimal (D.take k) : ℤ) * 10 ^ (D.length - k) + v = (decimal D : ℤ)) := by
  have hlo := hF.lo_le
  have hall' := allDigits_take_of_take_drop hk hN
  have hdec := decimal_take_add D k N hkN
  have hlenN : ((D.drop k).take N).length = N := by simp; omega
  have hlenkN : (D.take (k + N)).length = k + N := by simp; omega
  obtain ⟨hvlt, hvhi⟩ := decimal_take_lt_hi hF ((D.drop k).take N) hN (by omega)
  obtain ⟨hkNlt, hkNhi⟩ := decimal_take_lt_hi hF (D.take (k + N)) hall' (by omega)
  rw [hlenN] at hvlt
  rw [hlenkN] at hkNlt
  have hpow : (10 : ℤ) ^ (D.length - k) = 10 ^ (D.length - (k + N)) * 10 ^ N := by
    rw [← pow_add]; congr 1; omega
  have hres : (decimal (D.take k) : ℤ) * 10 ^ (D.length - k) + 10 ^ (D.length - (k + N)) * v =
      (decimal (D.take (k + N)) : ℤ) * 10 ^ (D.length - (k + N)) := by
    rw [hdec, hv, hpow]; ring
  have hp : (0 : ℤ) ≤ 10 ^ (D.length - (k + N)) := by positivity
  have hdk : (0 : ℤ) ≤ (decimal (D.take k) : ℤ) := by positivity
  have hdkN : (0 : ℤ) ≤ (decimal (D.take (k + N)) : ℤ) := by positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  -- the folded value is below 10^|D| ≤ 10^(c-1) ≤ hi
  have hbig : (decimal (D.take (k + N)) : ℤ) * 10 ^ (D.length - (k + N)) < 10 ^ D.length := by
    have : (10 : ℤ) ^ D.length = 10 ^ (k + N) * 10 ^ (D.length - (k + N)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    have hp' : (0 : ℤ) < 10 ^ (D.length - (k + N)) := by positivity
    nlinarith
  have hD10 : (10 : ℤ) ^ D.length ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hhi := hF.hi_ge
  have hres0 : 0 ≤ (decimal (D.take k) : ℤ) * 10 ^ (D.length - k) := by positivity
  have hprod : 0 ≤ 10 ^ (D.length - (k + N)) * v := mul_nonneg hp hv0
  refine ⟨hall', hres0, hv0, by rw [hv]; exact hvhi, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, hres, ?_⟩
  · omega
  · omega
  · intro heq
    have hN0 : D.length - (k + N) = 0 := by omega
    rw [hN0, pow_zero, one_mul] at hres
    rw [hres, heq, List.take_length]; simp

/-! ### The final result -/

theorem final_unchecked {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    (hH : Handover toInt lo hi c D0 D none) (hall : allDigits D) (resF : T)
    (hres : toInt resF = (decimal D : ℤ)) : PosResult toInt lo hi D0 (.Ok resF) := by
  obtain ⟨hlen, hlt, a, ha0, hahi, hfold, hb, hn, _⟩ := hH
  have ha : a = 0 := hn rfl
  subst ha
  show stdDigits lo hi false 0 D0 = .ok (toInt resF)
  rw [hfold, stdDigits_closed lo hi 0 D (le_refl 0) hF.lo_le hahi hb]
  obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D hall hlt
  rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
  have h2 : 0 * 10 ^ D.length + (decimal D : ℤ) ≤ hi := by simpa using hdhi
  rw [ite_eq_left_of_eq_true _ _ (eq_true h2), hres]
  simp

theorem final_checked {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8} {d : U8} {ct : T}
    (hH : Handover toInt lo hi c D0 D (some (d, ct))) (hall : allDigits D) (resF : T)
    (hres : toInt resF = (decimal D : ℤ)) (o : Option T)
    (ho : CheckedIs toInt lo hi (toInt ct + toInt resF) o) :
    core.option.Option.ok_or o ({ kind := .PosOverflow } : ParseIntErrorPublic)
      ⦃ r => PosResult toInt lo hi D0 r ⦄ := by
  obtain ⟨hlen, hlt, a, ha0, hahi, hfold, hb, _, hs⟩ := hH
  have hct := hs d ct rfl
  have hval : toInt ct + toInt resF = a * 10 ^ D.length + (decimal D : ℤ) := by rw [hct, hres]
  rw [hval] at ho
  have hclosed := stdDigits_closed lo hi a D ha0 hF.lo_le hahi hb
  rcases o with _ | z
  · have ho' : ¬ InRange lo hi (a * 10 ^ D.length + (decimal D : ℤ)) := ho
    simp only [InRange, not_and, not_le] at ho'
    have hneg : hi < a * 10 ^ D.length + (decimal D : ℤ) := by
      have hp : (0 : ℤ) ≤ a * 10 ^ D.length + (decimal D : ℤ) := by positivity
      exact ho' (by linarith [hF.lo_le])
    rw [core.option.Option.ok_or_none, WP.spec_ok]
    show ∃ k, stdDigits lo hi false 0 D0 = .error k ∧ kindLike .PosOverflow k
    refine ⟨.PosOverflow, ?_, Or.inl rfl⟩
    rw [hfold, hclosed, ite_eq_left_of_eq_true _ _ (eq_true hall),
      ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hneg))]
  · have ho' : InRange lo hi (a * 10 ^ D.length + (decimal D : ℤ)) ∧
        toInt z = a * 10 ^ D.length + (decimal D : ℤ) := ho
    obtain ⟨⟨_, hle⟩, hz⟩ := ho'
    rw [core.option.Option.ok_or_some, WP.spec_ok]
    show stdDigits lo hi false 0 D0 = .ok (toInt z)
    rw [hfold, hclosed, ite_eq_left_of_eq_true _ _ (eq_true hall), ite_eq_left_of_eq_true _ _ (eq_true hle), hz]

/-! ### A non-digit anywhere -/

theorem allDigits_drop {D : List U8} (h : allDigits D) (k : ℕ) : allDigits (D.drop k) :=
  fun b hb => h b (List.mem_of_mem_drop hb)

theorem allDigits_take {D : List U8} (h : allDigits D) (k : ℕ) : allDigits (D.take k) :=
  fun b hb => h b (List.mem_of_mem_take hb)

/-- A bad digit in the bytes: the reference says `InvalidDigit`. -/
theorem final_invalid {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {checked : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D checked) (hnot : ¬ allDigits D)
    (e : ParseIntErrorPublic) (he : e.kind = .InvalidDigit) : PosResult toInt lo hi D0 (.Err e) := by
  obtain ⟨_, _, a, ha0, hahi, hfold, hb, _, _⟩ := hH
  refine ⟨.InvalidDigit, ?_, Or.inl he⟩
  have hc := stdDigits_closed lo hi a D ha0 hF.lo_le hahi hb
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)] at hc
  exact hfold.trans hc

/-- Two leading digits, as `parse_2_chars_spec` states them. -/
theorem allDigits_take_two (l : List U8) (h : 2 ≤ l.length) :
    allDigits (l.take 2) ↔ isDigit l[0] ∧ isDigit l[1] := by
  match l, h with
  | b0 :: b1 :: rest, _ => simp [allDigits]

/-- The slice after a chunk, through `drop`. -/
theorem drop_drop_val (D : List U8) (k N : ℕ) : (D.drop k).drop N = D.drop (k + N) := by
  simp [List.drop_drop]

/-- `?` on an `Err`, with the identity conversion: the same error. -/
@[step]
theorem from_residual_same_spec (T E : Type) (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame E) (.Err e) ⦃ r => r = .Err e ⦄ := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.spec_ok]

/-! ### The chunk blocks

After each chunk block the `Sum` says: a final answer (`inl (inr _)`), which the reference
agrees with; or the state handed on (`inr _`), still inside the invariant. Blocks never produce
the `for` body's own `cont` value (`inl (inl _)`). -/

/-- The post-condition of a chunk block, for the inner levels (`inr` carries slice and value),
with a bound `M` on how many bytes may remain. -/
def BlockPost {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 D : List U8) (M : ℕ) {A : Type} :
    Sum (Sum A (core.result.Result T ParseIntErrorPublic × Slice U8 × Slice U8 × Slice U8 × Slice U8))
      (Slice U8 × T) → Prop
  | .inl (.inl _) => False
  | .inl (.inr (r, _, _, _, _)) => PosResult toInt lo hi D0 r
  | .inr (s', res') => BlockInv toInt D s' res' ∧ s'.val.length < M

/-- The same for the first block, whose `inr` also carries the range, unchanged (`it`). -/
def BlockPost1 {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 D : List U8) (M : ℕ) {A I : Type}
    (it : I) :
    Sum (Sum A (core.result.Result T ParseIntErrorPublic × Slice U8 × Slice U8 × Slice U8 × Slice U8))
      (Slice U8 × T × I) → Prop
  | .inl (.inl _) => False
  | .inl (.inr (r, _, _, _, _)) => PosResult toInt lo hi D0 r
  | .inr (s', res', i) => BlockInv toInt D s' res' ∧ s'.val.length < M ∧ i = it

theorem BlockPost.mono {T : Type} {toInt : T → ℤ} {lo hi : ℤ} {D0 D : List U8} {M M' : ℕ} {A : Type}
    (h : M ≤ M') (x : Sum (Sum A (core.result.Result T ParseIntErrorPublic × Slice U8 × Slice U8 ×
      Slice U8 × Slice U8)) (Slice U8 × T)) (hx : BlockPost toInt lo hi D0 D M x) :
    BlockPost toInt lo hi D0 D M' x := by
  rcases x with (c | ⟨r, _, _, _, _⟩) | ⟨s', res'⟩
  · exact hx
  · exact hx
  · exact ⟨hx.1, by have := hx.2; omega⟩

theorem WP.spec_mono_post {α : Type} {m : Result α} {p q : α → Prop} (h : m ⦃ p ⦄)
    (hpq : ∀ x, p x → q x) : m ⦃ q ⦄ := WP.spec_mono h hpq

/-- A conditional, by cases. -/
theorem WP.spec_ite {α : Type} {c : Prop} [Decidable c] {a b : Result α} {p : α → Prop}
    (h1 : c → a ⦃ p ⦄) (h2 : ¬ c → b ⦃ p ⦄) : (if c then a else b) ⦃ p ⦄ := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

/-- The digit count against the bit width: `10^(c-1) ≤ hi < 2^BITS`. -/
theorem c_le_of_bits {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ} {lo hi : ℤ}
    {c : ℕ} (hF : Faithful inst toInt lo hi c) (b : ℕ) (hb : (2 : ℤ) ^ b = hi - lo + 1)
    (hcases : b = 8 ∨ b = 16 ∨ b = 32 ∨ b = 64 ∨ b = 128) :
    (b < 16 → c ≤ 3) ∧ (b < 32 → c ≤ 5) ∧ (b < 64 → c ≤ 10) ∧ (b < 128 → c ≤ 20) ∧ c ≤ 39 := by
  have hlo := hF.lo_le
  have hge := hF.hi_ge
  have key : ∀ k, (10 : ℤ) ^ k ≤ 2 ^ b → k + 1 ≤ c → False → True := fun _ _ _ _ => trivial
  have bound : ∀ k, k + 1 ≤ c → (10 : ℤ) ^ k < 2 ^ b := by
    intro k hk
    have : (10 : ℤ) ^ k ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
  all_goals
    by_contra hc
    simp only [not_le] at hc
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> try norm_num at h
  · have := bound 3 (by omega); norm_num at this
  · have := bound 5 (by omega); norm_num at this
  · have := bound 5 (by omega); norm_num at this
  · have := bound 10 (by omega); norm_num at this
  · have := bound 5 (by omega); norm_num at this
  · have := bound 10 (by omega); norm_num at this
  · have := bound 20 (by omega); norm_num at this
  · have := bound 5 (by omega); norm_num at this
  · have := bound 10 (by omega); norm_num at this
  · have := bound 20 (by omega); norm_num at this
  all_goals have := bound 39 (by omega); norm_num at this

/-- The `for` body's own `cont` payload. -/
abbrev ContState (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 × T ×
  core.ops.range.Range I32 × Slice U8 × Slice U8 × Slice U8
/-- An early exit's payload: the answer, and the slices that ride along. -/
abbrev ExitState (T : Type) := core.result.Result T ParseIntErrorPublic × Slice U8 × Slice U8 ×
  Slice U8 × Slice U8
/-- What a chunk block hands on: the join of the three ways out. -/
abbrev Join (T : Type) := Sum (Sum (ContState T) (ExitState T)) (Slice U8 × T)

/-- The two-byte chunk (`src/parse.rs` lines 218-225 and 310-317), given at least two bytes
remain. -/
theorem chunk2_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {ch : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D ch)
    (s5 : Slice U8) (res1 : T) (u1 u2 u3 : Slice U8) (hinv : BlockInv toInt D s5 res1)
    (h2 : 2 ≤ s5.val.length) :
    (do
      let r ← parse_2_chars s5
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 => do
        let val3 ← inst.from_u16 val2
        let s9 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 2#usize } s5
        let b2 ← core.slice.Slice.is_empty s9
        if b2 = true then do
          let res2 ← inst.coreopsarithAddInst.add res1 val3
          match (generalizing := false) ch with
          | none => ok (Sum.inl (Sum.inr (core.result.Result.Ok res2, s9, u1, u2, u3)))
          | some p =>
            let (_, checked_t) := p
            do
            let o1 ← inst.add_checked checked_t res2
            let r1 ← core.option.Option.ok_or o1 { kind := core.num.error.IntErrorKind.PosOverflow }
            ok (Sum.inl (Sum.inr (r1, s9, u1, u2, u3)))
        else do
          let s10 ← inst.TREE
          let t ← s10.index_usize s9.len
          let t1 ← inst.coreopsarithMulInst.mul t val3
          let res2 ← inst.coreopsarithAddInst.add res1 t1
          ok (Sum.inr (s9, res2))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame ParseIntErrorPublic) residual
        ok (Sum.inl (Sum.inr (r1, s5, u1, u2, u3))) : Result (Join T))
      ⦃ BlockPost toInt lo hi D0 D (s5.val.length - 2 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s5.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hAC := hF.add_checked
  have hAdd := hF.add
  have hMul := hF.mul
  have hTR := hF.TREE
  have hF16 := hF.from_u16
  step with parse_2_chars_spec s5 h2 as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- two digits
    simp only at hr hcf
    subst hcf
    have hN : allDigits ((D.drop k).take 2) := by
      rw [← hs5, allDigits_take_two _ h2]; exact ⟨hr.1, hr.2.1⟩
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 2) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2.2
    obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step hF D hDlt k 2 (by omega) hallk hN (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 2) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk was the last of the bytes: the number is complete
      rename_i hb2t
      have hempty : k + 2 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have hadd : InRange lo hi (toInt res1 + toInt val3) := by
        rw [hres1, hval3']
        have := hfull hempty
        have hlo := hF.lo_le
        have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
        obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D (by have := hall'; rwa [hempty, List.take_length] at this) hDlt
        constructor <;> omega
      step with hAdd res1 val3 hadd as ⟨res2, hres2⟩
      have hres2' : toInt res2 = (decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact final_unchecked hF hH hallD res2 hres2'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hallD res2 hres2' o1 ho1)
        intro r1 hr1
        step*
        exact hr1
    · -- more bytes follow: scale and accumulate
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 2) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
      have htv : toInt t = 10 ^ (D.length - (k + 2)) := by
        rw [ht]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt t * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul t val3 hmr' as ⟨t1, ht1⟩
      have har' : InRange lo hi (toInt res1 + toInt t1) := by rw [ht1, htv, hval3', hres1]; exact har
      step with hAdd res1 t1 har' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hk2 : k + 2 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 2, hk2, hs9', hall', by rw [hres2, ht1, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [← allDigits_take_two _ h2, hs5]
      exact allDigits_take (allDigits_drop hall k) 2
    step as ⟨r1, hr1⟩
    subst hr1
    exact final_invalid hF hH hnot e hkind

/-- The 4-byte chunk (`src/parse.rs` lines 229-236 and 299-306), given at least 4 bytes remain. -/
theorem chunk4_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {ch : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D ch)
    (s5 : Slice U8) (res1 : T) (u1 u2 u3 : Slice U8) (hinv : BlockInv toInt D s5 res1)
    (h2 : 4 ≤ s5.val.length) :
    (do
      let r ← parse_4_chars s5
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 => do
        let val3 ← inst.from_u16 val2
        let s9 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 4#usize } s5
        let b2 ← core.slice.Slice.is_empty s9
        if b2 = true then do
          let res2 ← inst.coreopsarithAddInst.add res1 val3
          match (generalizing := false) ch with
          | none => ok (Sum.inl (Sum.inr (core.result.Result.Ok res2, s9, u1, u2, u3)))
          | some p =>
            let (_, checked_t) := p
            do
            let o1 ← inst.add_checked checked_t res2
            let r1 ← core.option.Option.ok_or o1 { kind := core.num.error.IntErrorKind.PosOverflow }
            ok (Sum.inl (Sum.inr (r1, s9, u1, u2, u3)))
        else do
          let s10 ← inst.TREE
          let t ← s10.index_usize s9.len
          let t1 ← inst.coreopsarithMulInst.mul t val3
          let res2 ← inst.coreopsarithAddInst.add res1 t1
          ok (Sum.inr (s9, res2))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame ParseIntErrorPublic) residual
        ok (Sum.inl (Sum.inr (r1, s5, u1, u2, u3))) : Result (Join T))
      ⦃ BlockPost toInt lo hi D0 D (s5.val.length - 4 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s5.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hAC := hF.add_checked
  have hAdd := hF.add
  have hMul := hF.mul
  have hTR := hF.TREE
  have hF16 := hF.from_u16
  step with parse_4_chars_spec s5 h2 as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- two digits
    simp only at hr hcf
    subst hcf
    have hN : allDigits ((D.drop k).take 4) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 4) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step hF D hDlt k 4 (by omega) hallk hN (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 4) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk was the last of the bytes: the number is complete
      rename_i hb2t
      have hempty : k + 4 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have hadd : InRange lo hi (toInt res1 + toInt val3) := by
        rw [hres1, hval3']
        have := hfull hempty
        have hlo := hF.lo_le
        have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
        obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D (by have := hall'; rwa [hempty, List.take_length] at this) hDlt
        constructor <;> omega
      step with hAdd res1 val3 hadd as ⟨res2, hres2⟩
      have hres2' : toInt res2 = (decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact final_unchecked hF hH hallD res2 hres2'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hallD res2 hres2' o1 ho1)
        intro r1 hr1
        step*
        exact hr1
    · -- more bytes follow: scale and accumulate
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 4) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
      have htv : toInt t = 10 ^ (D.length - (k + 4)) := by
        rw [ht]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt t * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul t val3 hmr' as ⟨t1, ht1⟩
      have har' : InRange lo hi (toInt res1 + toInt t1) := by rw [ht1, htv, hval3', hres1]; exact har
      step with hAdd res1 t1 har' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hk4 : k + 4 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 4, hk4, hs9', hall', by rw [hres2, ht1, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 4
    step as ⟨r1, hr1⟩
    subst hr1
    exact final_invalid hF hH hnot e hkind

/-- The 8-byte chunk (`src/parse.rs` lines 240-247 and 288-295), given at least 8 bytes remain. -/
theorem chunk8_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {ch : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D ch)
    (s5 : Slice U8) (res1 : T) (u1 u2 u3 : Slice U8) (hinv : BlockInv toInt D s5 res1)
    (h2 : 8 ≤ s5.val.length) :
    (do
      let r ← parse_8_chars s5
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 => do
        let val3 ← inst.from_u32 val2
        let s9 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 8#usize } s5
        let b2 ← core.slice.Slice.is_empty s9
        if b2 = true then do
          let res2 ← inst.coreopsarithAddInst.add res1 val3
          match (generalizing := false) ch with
          | none => ok (Sum.inl (Sum.inr (core.result.Result.Ok res2, s9, u1, u2, u3)))
          | some p =>
            let (_, checked_t) := p
            do
            let o1 ← inst.add_checked checked_t res2
            let r1 ← core.option.Option.ok_or o1 { kind := core.num.error.IntErrorKind.PosOverflow }
            ok (Sum.inl (Sum.inr (r1, s9, u1, u2, u3)))
        else do
          let s10 ← inst.TREE
          let t ← s10.index_usize s9.len
          let t1 ← inst.coreopsarithMulInst.mul t val3
          let res2 ← inst.coreopsarithAddInst.add res1 t1
          ok (Sum.inr (s9, res2))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame ParseIntErrorPublic) residual
        ok (Sum.inl (Sum.inr (r1, s5, u1, u2, u3))) : Result (Join T))
      ⦃ BlockPost toInt lo hi D0 D (s5.val.length - 8 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s5.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hAC := hF.add_checked
  have hAdd := hF.add
  have hMul := hF.mul
  have hTR := hF.TREE
  have hF32 := hF.from_u32
  step with parse_8_chars_spec s5 h2 as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- two digits
    simp only at hr hcf
    subst hcf
    have hN : allDigits ((D.drop k).take 8) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 8) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step hF D hDlt k 8 (by omega) hallk hN (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 8) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk was the last of the bytes: the number is complete
      rename_i hb2t
      have hempty : k + 8 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have hadd : InRange lo hi (toInt res1 + toInt val3) := by
        rw [hres1, hval3']
        have := hfull hempty
        have hlo := hF.lo_le
        have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
        obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D (by have := hall'; rwa [hempty, List.take_length] at this) hDlt
        constructor <;> omega
      step with hAdd res1 val3 hadd as ⟨res2, hres2⟩
      have hres2' : toInt res2 = (decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact final_unchecked hF hH hallD res2 hres2'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hallD res2 hres2' o1 ho1)
        intro r1 hr1
        step*
        exact hr1
    · -- more bytes follow: scale and accumulate
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 8) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
      have htv : toInt t = 10 ^ (D.length - (k + 8)) := by
        rw [ht]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt t * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul t val3 hmr' as ⟨t1, ht1⟩
      have har' : InRange lo hi (toInt res1 + toInt t1) := by rw [ht1, htv, hval3', hres1]; exact har
      step with hAdd res1 t1 har' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hk8 : k + 8 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 8, hk8, hs9', hall', by rw [hres2, ht1, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 8
    step as ⟨r1, hr1⟩
    subst hr1
    exact final_invalid hF hH hnot e hkind

/-- The 16-byte chunk (`src/parse.rs` lines 251-259 and 276-284), given at least 16 bytes remain. -/
theorem chunk16_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {ch : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D ch)
    (s5 : Slice U8) (res1 : T) (u1 u2 u3 : Slice U8) (hinv : BlockInv toInt D s5 res1)
    (h2 : 16 ≤ s5.val.length) :
    (do
      let r ← parse_16_chars s5
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 => do
        let val3 ← inst.from_u64 val2
        let s9 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 16#usize } s5
        let b2 ← core.slice.Slice.is_empty s9
        if b2 = true then do
          let res2 ← inst.coreopsarithAddInst.add res1 val3
          match (generalizing := false) ch with
          | none => ok (Sum.inl (Sum.inr (core.result.Result.Ok res2, s9, u1, u2, u3)))
          | some p =>
            let (_, checked_t) := p
            do
            let o1 ← inst.add_checked checked_t res2
            let r1 ← core.option.Option.ok_or o1 { kind := core.num.error.IntErrorKind.PosOverflow }
            ok (Sum.inl (Sum.inr (r1, s9, u1, u2, u3)))
        else do
          let s10 ← inst.TREE
          let t ← s10.index_usize s9.len
          let t1 ← inst.coreopsarithMulInst.mul t val3
          let res2 ← inst.coreopsarithAddInst.add res1 t1
          ok (Sum.inr (s9, res2))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame ParseIntErrorPublic) residual
        ok (Sum.inl (Sum.inr (r1, s5, u1, u2, u3))) : Result (Join T))
      ⦃ BlockPost toInt lo hi D0 D (s5.val.length - 16 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s5.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hAC := hF.add_checked
  have hAdd := hF.add
  have hMul := hF.mul
  have hTR := hF.TREE
  have hF64 := hF.from_u64
  step with parse_16_chars_spec s5 h2 as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- two digits
    simp only at hr hcf
    subst hcf
    have hN : allDigits ((D.drop k).take 16) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 16) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step hF D hDlt k 16 (by omega) hallk hN (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 16) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk was the last of the bytes: the number is complete
      rename_i hb2t
      have hempty : k + 16 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have hadd : InRange lo hi (toInt res1 + toInt val3) := by
        rw [hres1, hval3']
        have := hfull hempty
        have hlo := hF.lo_le
        have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
        obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D (by have := hall'; rwa [hempty, List.take_length] at this) hDlt
        constructor <;> omega
      step with hAdd res1 val3 hadd as ⟨res2, hres2⟩
      have hres2' : toInt res2 = (decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact final_unchecked hF hH hallD res2 hres2'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hallD res2 hres2' o1 ho1)
        intro r1 hr1
        step*
        exact hr1
    · -- more bytes follow: scale and accumulate
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 16) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
      have htv : toInt t = 10 ^ (D.length - (k + 16)) := by
        rw [ht]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt t * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul t val3 hmr' as ⟨t1, ht1⟩
      have har' : InRange lo hi (toInt res1 + toInt t1) := by rw [ht1, htv, hval3', hres1]; exact har
      step with hAdd res1 t1 har' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hk16 : k + 16 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 16, hk16, hs9', hall', by rw [hres2, ht1, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 16
    step as ⟨r1, hr1⟩
    subst hr1
    exact final_invalid hF hH hnot e hkind

/-- The 32-byte chunk (`src/parse.rs` lines 264-272), given at least 32 bytes remain. -/
theorem chunk32_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) {D0 D : List U8}
    {ch : Option (U8 × T)} (hH : Handover toInt lo hi c D0 D ch)
    (s5 : Slice U8) (res1 : T) (u1 u2 u3 : Slice U8) (hinv : BlockInv toInt D s5 res1)
    (h2 : 32 ≤ s5.val.length) :
    (do
      let r ← parse_32_chars s5
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 => do
        let val3 ← inst.from_u128 val2
        let s9 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 32#usize } s5
        let b2 ← core.slice.Slice.is_empty s9
        if b2 = true then do
          let res2 ← inst.coreopsarithAddInst.add res1 val3
          match (generalizing := false) ch with
          | none => ok (Sum.inl (Sum.inr (core.result.Result.Ok res2, s9, u1, u2, u3)))
          | some p =>
            let (_, checked_t) := p
            do
            let o1 ← inst.add_checked checked_t res2
            let r1 ← core.option.Option.ok_or o1 { kind := core.num.error.IntErrorKind.PosOverflow }
            ok (Sum.inl (Sum.inr (r1, s9, u1, u2, u3)))
        else do
          let s10 ← inst.TREE
          let t ← s10.index_usize s9.len
          let t1 ← inst.coreopsarithMulInst.mul t val3
          let res2 ← inst.coreopsarithAddInst.add res1 t1
          ok (Sum.inr (s9, res2))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame ParseIntErrorPublic) residual
        ok (Sum.inl (Sum.inr (r1, s5, u1, u2, u3))) : Result (Join T))
      ⦃ BlockPost toInt lo hi D0 D (s5.val.length - 32 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s5.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hAC := hF.add_checked
  have hAdd := hF.add
  have hMul := hF.mul
  have hTR := hF.TREE
  have hF128 := hF.from_u128
  step with parse_32_chars_spec s5 h2 as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- two digits
    simp only at hr hcf
    subst hcf
    have hN : allDigits ((D.drop k).take 32) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 32) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step hF D hDlt k 32 (by omega) hallk hN (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 32) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk was the last of the bytes: the number is complete
      rename_i hb2t
      have hempty : k + 32 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have hadd : InRange lo hi (toInt res1 + toInt val3) := by
        rw [hres1, hval3']
        have := hfull hempty
        have hlo := hF.lo_le
        have hp : (0 : ℤ) ≤ (decimal D : ℤ) := by positivity
        obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF D (by have := hall'; rwa [hempty, List.take_length] at this) hDlt
        constructor <;> omega
      step with hAdd res1 val3 hadd as ⟨res2, hres2⟩
      have hres2' : toInt res2 = (decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact final_unchecked hF hH hallD res2 hres2'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hallD res2 hres2' o1 ho1)
        intro r1 hr1
        step*
        exact hr1
    · -- more bytes follow: scale and accumulate
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 32) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
      have htv : toInt t = 10 ^ (D.length - (k + 32)) := by
        rw [ht]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt t * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul t val3 hmr' as ⟨t1, ht1⟩
      have har' : InRange lo hi (toInt res1 + toInt t1) := by rw [ht1, htv, hval3', hres1]; exact har
      step with hAdd res1 t1 har' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hk32 : k + 32 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 32, hk32, hs9', hall', by rw [hres2, ht1, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 32
    step as ⟨r1, hr1⟩
    subst hr1
    exact final_invalid hF hH hnot e hkind


/-- The join after a chunk block: the `cont` value never comes out of a block, a final answer
passes through, and the handed-on state is either passed through too or continues. -/
syntax "join " ident ident ident : tactic
macro_rules
  | `(tactic| join $s $r $h) => `(tactic| (
      rintro x $h
      rcases x with (c | b1) | ⟨$s, $r⟩
      · exact ($h : False).elim
      · first
          | exact (WP.spec_ok _).mpr $h
          | (rcases b1 with ⟨r', _, _, _, _⟩; exact (WP.spec_ok _).mpr $h)
      try (rw [WP.spec_ok]; exact $h)))

/-- A chunk guarded by the alignment test, from a state with `M` bytes or fewer. -/
syntax "guarded " term:max term:max : tactic
macro_rules
  | `(tactic| guarded $lem $hinv) => `(tactic| (
      refine WP.spec_ite (fun _ => ?_) (fun _ => ?_)
      · exact WP.spec_mono_post $lem (BlockPost.mono (by omega))
      · refine (WP.spec_ok _).mpr ?_
        exact ⟨$hinv, by omega⟩))

/-- Close an `ok` with its post, the expected type known first. -/
syntax "okpost " term : tactic
macro_rules
  | `(tactic| okpost $t) => `(tactic| (refine (WP.spec_ok _).mpr ?_; exact $t))

/-- `N ≤ |s|` from the guard `s.len ≥ N`. -/
theorem len_ge_of_guard {N : ℕ} (s : Slice U8) (n : Usize) (hn : n.val = N) (h : s.len ≥ n) :
    N ≤ (↑s : List U8).length := by
  have := (UScalar.le_equiv n s.len).mp h
  rw [Slice.len_val, hn] at this
  exact this

/-! ### The loop -/

theorem parse_inner_loop2_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (D0 : List U8) (s : Slice U8)
    (is_signed_ty : Bool) (checked : Option (U8 × T)) (val val1 : U8) (res : T)
    (s1 s2 s3 : Slice U8) (hH : Handover toInt lo hi c D0 s.val checked) (hres : toInt res = 0)
    (hv1 : ∃ d, s.val[0]? = some d ∧ isDigit d ∧ val1.val = d.val - 48) :
    parse.parse_inner_loop2 inst { start := 0#i32, «end» := 1#i32 } s is_signed_ty checked val val1
        res s1 s2 s3
      ⦃ (r : core.result.Result T ParseIntErrorPublic) => PosResult toInt lo hi D0 r ⦄ := by
  unfold parse.parse_inner_loop2
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range I32 × Slice U8 × Bool × Option (U8 × T) × U8 × U8 × T ×
        Slice U8 × Slice U8 × Slice U8) => (p.1.«end».val - p.1.start.val).toNat)
    (fun (p : core.ops.range.Range I32 × Slice U8 × Bool × Option (U8 × T) × U8 × U8 × T ×
        Slice U8 × Slice U8 × Slice U8) =>
      match p with
      | (iter, s', b, ch, v, v1', res', t1, t2, t3) =>
        ch = checked ∧ iter.«end».val = 1 ∧
        ((iter.start.val = 0 ∧ s' = s ∧ v1' = val1 ∧ toInt res' = 0) ∨
         (iter.start.val = 1 ∧ allDigits s.val ∧ toInt res' = (decimal s.val : ℤ))))
  · rintro ⟨iter, s', b, ch, v, v1', res', t1, t2, t3⟩ ⟨rfl, hend, hcase⟩
    have hAC := hF.add_checked
    have hAdd := hF.add
    have hMul := hF.mul
    have hTR := hF.TREE
    have hF8 := hF.from_u8
    have hF16 := hF.from_u16
    have hF32 := hF.from_u32
    have hF64 := hF.from_u64
    have hF128 := hF.from_u128
    have hBITS := hF.BITS
    have hp2 := parse_2_chars_spec
    have hp4 := parse_4_chars_spec
    have hp8 := parse_8_chars_spec
    have hp16 := parse_16_chars_spec
    have hp32 := parse_32_chars_spec
    unfold parse.parse_inner_loop2.body
    step as ⟨o, iter1, hnext, hend1⟩
    rcases hcase with ⟨hstart, rfl, rfl, hres'⟩ | ⟨hstart, hall, hres'⟩
    · -- first iteration: the block
      rw [hstart, hend] at hnext
      simp only [show (0 : ℤ) < 1 from by norm_num, ite_true] at hnext
      obtain ⟨rfl, hstart1⟩ := hnext
      step*
      have hDlt := hH.len_lt
      have hDpos := hH.len_pos
      obtain ⟨d, hd0, hdd, hv1d⟩ := hv1
      have hcons := cons_of_getElem?_zero _ hd0
      have hd48 : (v1'.val : ℤ) = (d.val : ℤ) - 48 := by have := hdd.1; omega
      refine WP.spec_bind (Pₘ := BlockPost1 toInt lo hi D0 (↑s' : List U8) ((↑s' : List U8).length + 1) iter1) ?_ ?_
      · -- the first block: one byte, when the slice is odd for `u16`
        split
        · rename_i hb
          have hN : allDigits (((↑s' : List U8).drop 0).take 1) := by
            rw [List.drop_zero, hcons]; simp [allDigits, hdd]
          have hv : (v1'.val : ℤ) = (decimal (((↑s' : List U8).drop 0).take 1) : ℤ) := by
            rw [List.drop_zero, hcons]; simp [decimal]; omega
          obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
            chunk_step hF (↑s' : List U8) hDlt 0 1 (by omega) (by simp [allDigits]) hN _ hv
          step as ⟨val_t, hvt⟩
          have hvt' : toInt val_t = (v1'.val : ℤ) := hvt hvhi
          step as ⟨s5, hs5, hs5len⟩
          have hs5' : (↑s5 : List U8) = (↑s' : List U8).drop (0 + 1) := by rw [hs5]
          step as ⟨b1, hb1⟩
          split
          · -- the byte was the whole slice
            rename_i hb1t
            have hempty : 0 + 1 = (↑s' : List U8).length := by
              have h5z : (↑s5 : List U8) = [] := by
                have h := hb1; rw [hb1t] at h; simp [Slice.length] at h; exact h
              rw [hs5', List.drop_eq_nil_iff] at h5z; omega
            have hres2' : toInt val_t = (decimal (↑s' : List U8) : ℤ) := by
              rw [hvt']; have := hfull hempty; simpa [decimal] using this
            have hallD : allDigits (↑s' : List U8) := by
              have := hall'; rwa [hempty, List.take_length] at this
            revert hH
            rcases hck : ch with _ | ⟨d', ct⟩ <;> intro hH <;> dsimp only
            · rw [WP.spec_ok]
              exact final_unchecked hF hH hallD val_t hres2'
            · step as ⟨o1, ho1⟩
              apply WP.spec_bind (final_checked hF hH hallD val_t hres2' o1 ho1)
              intro r1 hr1
              step*
              exact hr1
          · -- more bytes follow: weight the digit
            step as ⟨tr, htrlen, htr⟩
            have hs5l : s5.len.val = (↑s' : List U8).length - (0 + 1) := by
              rw [Slice.len_val]; simp [Slice.length, hs5']
            step with Slice.index_usize_spec tr s5.len
              (by rw [hs5l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t, ht⟩
            have htv : toInt t = 10 ^ ((↑s' : List U8).length - (0 + 1)) := by
              rw [ht]; simp only [hs5l]; exact htr _ (by omega)
            have hmr' : InRange lo hi (toInt val_t * toInt t) := by
              rw [htv, hvt', mul_comm]; exact hmr
            step with hMul val_t t hmr' as ⟨res1, hres1⟩
            have hb1f : ¬ b1 = true := by assumption
            have hk1 : 0 + 1 < (↑s' : List U8).length := by
              have h0 : ¬ (↑s5 : List U8).length = 0 := by
                intro h0; apply hb1f; rw [hb1]; simp [Slice.length, h0]
              rw [hs5', List.length_drop] at h0; omega
            have hd0 : decimal ([] : List U8) = 0 := rfl
            refine ⟨⟨0 + 1, hk1, hs5', hall', ?_⟩, by rw [hs5', List.length_drop]; omega, rfl⟩
            rw [hres1, hvt', htv, ← hresnew]
            simp only [List.take_zero, hd0, Nat.cast_zero, zero_mul, zero_add, mul_comm]
        · -- aligned already: nothing consumed yet
          rw [WP.spec_ok]
          exact ⟨⟨0, hDpos, by simp, by simp [allDigits], by simp [hres', decimal]⟩, by omega, rfl⟩
      · -- the join after the first block
        rintro s4 hs4
        rcases s4 with (c | b1) | ⟨s5, res1, iter2⟩
        · exact (hs4 : False).elim
        · rcases b1 with ⟨r, _, _, _, _⟩
          exact (WP.spec_ok _).mpr hs4
        · dsimp only
          obtain ⟨hinv5, hlen5, rfl⟩ := hs4
          -- level 2: at least two bytes remain and the type has 8 bits; afterwards fewer than two
          refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
          · refine WP.spec_ite (fun hg2 => ?_) (fun hg2 => ?_)
            · have h2 := len_ge_of_guard (N := 2) s5 2#usize (by simp) hg2
              step as ⟨i1, hi1, hcases⟩
              obtain ⟨hc16, hc32, hc64, hc128, hc39⟩ := c_le_of_bits hF i1.val hi1 hcases
              refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
              · refine WP.spec_ite (fun hb8 => ?_) (fun hb8 => ?_)
                · step as ⟨b1⟩
                  refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) ((↑s5 : List U8).length + 1)) ?_ ?_
                  · guarded (chunk2_spec hF hH s5 res1 t1 t2 t3 hinv5 h2) hinv5
                  · join s9 res2 hs8
                    obtain ⟨hinv9, hlen9⟩ := hs8
                    -- level 4: afterwards fewer than four
                    refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                    · refine WP.spec_ite (fun hg4 => ?_) (fun hg4 => ?_)
                      · have h4 := len_ge_of_guard (N := 4) s9 4#usize (by simp) hg4
                        refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                        · refine WP.spec_ite (fun hb16 => ?_) (fun hb16 => ?_)
                          · step as ⟨b2⟩
                            refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) ((↑s9 : List U8).length + 1)) ?_ ?_
                            · guarded (chunk4_spec hF hH s9 res2 t1 t2 t3 hinv9 h4) hinv9
                            · join s13 res3 hs12
                              obtain ⟨hinv13, hlen13⟩ := hs12
                              -- level 8: afterwards fewer than eight
                              refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                              · refine WP.spec_ite (fun hg8 => ?_) (fun hg8 => ?_)
                                · have h8 := len_ge_of_guard (N := 8) s13 8#usize (by simp) hg8
                                  refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                                  · refine WP.spec_ite (fun hb32 => ?_) (fun hb32 => ?_)
                                    · step as ⟨b3⟩
                                      refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) ((↑s13 : List U8).length + 1)) ?_ ?_
                                      · guarded (chunk8_spec hF hH s13 res3 t1 t2 t3 hinv13 h8) hinv13
                                      · join s17 res4 hs16
                                        obtain ⟨hinv17, hlen17⟩ := hs16
                                        -- level 16: afterwards fewer than sixteen
                                        refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                        · refine WP.spec_ite (fun hg16 => ?_) (fun hg16 => ?_)
                                          · have h16 := len_ge_of_guard (N := 16) s17 16#usize (by simp) hg16
                                            refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                            · refine WP.spec_ite (fun hb64 => ?_) (fun hb64 => ?_)
                                              · step as ⟨b4⟩
                                                refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) ((↑s17 : List U8).length + 1)) ?_ ?_
                                                · guarded (chunk16_spec hF hH s17 res4 t1 t2 t3 hinv17 h16) hinv17
                                                · join s21 res5 hs20
                                                  obtain ⟨hinv21, hlen21⟩ := hs20
                                                  -- level 32: afterwards fewer than 32
                                                  refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 32) ?_ ?_
                                                  · refine WP.spec_ite (fun hg32 => ?_) (fun hg32 => ?_)
                                                    · have h32 := len_ge_of_guard (N := 32) s21 32#usize (by simp) hg32
                                                      refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 32) ?_ ?_
                                                      · refine WP.spec_ite (fun hb128 => ?_) (fun hb128 => ?_)
                                                        · exact WP.spec_mono_post (chunk32_spec hF hH s21 res5 t1 t2 t3 hinv21 h32)
                                                            (BlockPost.mono (by obtain ⟨k, hk, hs21v, _, _⟩ := hinv21; rw [hs21v, List.length_drop]; omega))
                                                        · -- fewer than 128 bits: at most 20 digits, so fewer than 32 bytes
                                                          exfalso
                                                          have hb : i1.val < 128 := by
                                                            have := mt (UScalar.le_equiv 128#u32 i1).mpr hb128; simp at this; omega
                                                          have := hc128 hb; have := hDlt
                                                          obtain ⟨k, hk, hs21v, _, _⟩ := hinv21
                                                          rw [hs21v, List.length_drop] at h32; omega
                                                      · join s23 res6 hs22
                                                    · okpost ⟨hinv21, by
                                                        have := mt (UScalar.le_equiv 32#usize s21.len).mpr hg32
                                                        simp at this; omega⟩
                                                  · join s23 res6 hs22
                                                    obtain ⟨hinv23, hlen23⟩ := hs22
                                                    -- the aligned sixteen: afterwards fewer than sixteen
                                                    refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                                    · refine WP.spec_ite (fun hg16b => ?_) (fun hg16b => ?_)
                                                      · exact WP.spec_mono_post (chunk16_spec hF hH s23 res6 t1 t2 t3 hinv23 (len_ge_of_guard (N := 16) s23 16#usize (by simp) hg16b))
                                                          (BlockPost.mono (by omega))
                                                      · okpost ⟨hinv23, by
                                                          have := mt (UScalar.le_equiv 16#usize s23.len).mpr hg16b
                                                          simp at this; omega⟩
                                                    · join s25 res7 hs24
                                              · -- fewer than 64 bits: at most 10 digits
                                                exfalso
                                                have hb : i1.val < 64 := by
                                                  have := mt (UScalar.le_equiv 64#u32 i1).mpr hb64; simp at this; omega
                                                have := hc64 hb; have := hDlt
                                                obtain ⟨k, hk, hs17v, _, _⟩ := hinv17
                                                rw [hs17v, List.length_drop] at h16; omega
                                            · join s19 res5 hs18
                                          · okpost ⟨hinv17, by
                                              have := mt (UScalar.le_equiv 16#usize s17.len).mpr hg16
                                              simp at this; omega⟩
                                        · join s19 res5 hs18
                                          obtain ⟨hinv19, hlen19⟩ := hs18
                                          -- the aligned eight: afterwards fewer than eight
                                          refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                                          · refine WP.spec_ite (fun hg8b => ?_) (fun hg8b => ?_)
                                            · exact WP.spec_mono_post (chunk8_spec hF hH s19 res5 t1 t2 t3 hinv19 (len_ge_of_guard (N := 8) s19 8#usize (by simp) hg8b))
                                                (BlockPost.mono (by omega))
                                            · okpost ⟨hinv19, by
                                                have := mt (UScalar.le_equiv 8#usize s19.len).mpr hg8b
                                                simp at this; omega⟩
                                          · join s21 res6 hs20
                                    · -- fewer than 32 bits: at most 5 digits
                                      exfalso
                                      have hb : i1.val < 32 := by
                                        have := mt (UScalar.le_equiv 32#u32 i1).mpr hb32; simp at this; omega
                                      have := hc32 hb; have := hDlt
                                      obtain ⟨k, hk, hs13v, _, _⟩ := hinv13
                                      rw [hs13v, List.length_drop] at h8; omega
                                  · join s15 res4 hs14
                                · okpost ⟨hinv13, by
                                    have := mt (UScalar.le_equiv 8#usize s13.len).mpr hg8
                                    simp at this; omega⟩
                              · join s15 res4 hs14
                                obtain ⟨hinv15, hlen15⟩ := hs14
                                -- the aligned four: afterwards fewer than four
                                refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                                · refine WP.spec_ite (fun hg4b => ?_) (fun hg4b => ?_)
                                  · exact WP.spec_mono_post (chunk4_spec hF hH s15 res4 t1 t2 t3 hinv15 (len_ge_of_guard (N := 4) s15 4#usize (by simp) hg4b))
                                      (BlockPost.mono (by omega))
                                  · okpost ⟨hinv15, by
                                      have := mt (UScalar.le_equiv 4#usize s15.len).mpr hg4b
                                      simp at this; omega⟩
                                · join s17 res5 hs16
                          · -- fewer than 16 bits: at most 3 digits
                            exfalso
                            have hb : i1.val < 16 := by
                              have := mt (UScalar.le_equiv 16#u32 i1).mpr hb16; simp at this; omega
                            have := hc16 hb; have := hDlt
                            obtain ⟨k, hk, hs9v, _, _⟩ := hinv9
                            rw [hs9v, List.length_drop] at h4; omega
                        · join s11 res3 hs10
                      · okpost ⟨hinv9, by
                          have := mt (UScalar.le_equiv 4#usize s9.len).mpr hg4
                          simp at this; omega⟩
                    · join s11 res3 hs10
                      obtain ⟨hinv11, hlen11⟩ := hs10
                      -- the aligned pair: afterwards fewer than two
                      refine WP.spec_bind (Pₘ := BlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
                      · refine WP.spec_ite (fun hg2b => ?_) (fun hg2b => ?_)
                        · exact WP.spec_mono_post (chunk2_spec hF hH s11 res3 t1 t2 t3 hinv11 (len_ge_of_guard (N := 2) s11 2#usize (by simp) hg2b))
                            (BlockPost.mono (by omega))
                        · okpost ⟨hinv11, by
                            have := mt (UScalar.le_equiv 2#usize s11.len).mpr hg2b
                            simp at this; omega⟩
                      · join s13 res4 hs12
                · -- fewer than 8 bits: no such type
                  exfalso
                  have hb : i1.val < 8 := by
                    have := mt (UScalar.le_equiv 8#u32 i1).mpr hb8; simp at this; omega
                  rcases hcases with h | h | h | h | h <;> omega
              · join s7 res2 hs6
            · okpost ⟨hinv5, by
                have := mt (UScalar.le_equiv 2#usize s5.len).mpr hg2
                simp at this; omega⟩
          · join s7 res2 hs6
            dsimp only
            -- the tail: exactly one byte is left
            obtain ⟨⟨k, hk, hs7, hallk, hres2⟩, hlen7⟩ := hs6
            have hk1 : k + 1 = (↑s' : List U8).length := by
              rw [hs7, List.length_drop] at hlen7; omega
            step as ⟨o1, ho1⟩
            rcases o1 with _ | val2
            · exfalso
              have : (↑s7 : List U8) ≠ [] := by
                rw [hs7]; intro h; rw [List.drop_eq_nil_iff] at h; omega
              exact this (List.head?_eq_none_iff.mp ho1.symm)
            · have hhead : (↑s7 : List U8).head? = some val2 := ho1.symm
              have hcons7 : (↑s7 : List U8) = val2 :: (↑s7 : List U8).tail := by
                apply cons_of_getElem?_zero
                rcases h : (↑s7 : List U8) with _ | ⟨a, l⟩
                · rw [h] at hhead; simp at hhead
                · rw [h] at hhead; simpa using hhead
              have hval2 : ((↑s' : List U8).drop k).take 1 = [val2] := by
                rw [← hs7, hcons7]; simp
              step as ⟨val3, hval3⟩
              have hw := U8.wrapping_sub_48_val val2
              have hvb := U8.val_lt_256 val2
              have hdig := wrapping_digit_test val2.val hvb
              refine WP.spec_ite (fun hgt => ?_) (fun hle => ?_)
              · -- not a digit
                have h9 : 9 < val3.val := by have := UScalar.lt_equiv 9#u8 val3 |>.mp hgt; simpa using this
                rw [hval3, hw] at h9
                have hnd : ¬ isDigit val2 := by show ¬ (48 ≤ val2.val ∧ val2.val ≤ 57); omega
                have hnot : ¬ allDigits (↑s' : List U8) := by
                  intro hall
                  apply hnd
                  have := allDigits_drop hall k
                  rw [← hs7, hcons7] at this
                  exact this val2 (by simp)
                rw [WP.spec_ok]
                exact final_invalid hF hH hnot _ rfl
              · -- a digit: the last one
                have h9 : val3.val ≤ 9 := by
                  have := mt (UScalar.lt_equiv 9#u8 val3).mpr hle; simp at this; omega
                rw [hval3, hw] at h9
                have hdg : isDigit val2 := by show 48 ≤ val2.val ∧ val2.val ≤ 57; omega
                have hN : allDigits (((↑s' : List U8).drop k).take 1) := by
                  rw [hval2]; simp [allDigits, hdg]
                have hv : (val3.val : ℤ) = (decimal (((↑s' : List U8).drop k).take 1) : ℤ) := by
                  rw [hval2, hval3, hw]; simp [decimal]; omega
                obtain ⟨hall', hres0, hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
                  chunk_step hF (↑s' : List U8) hDlt k 1 (by omega) hallk hN _ hv
                step as ⟨tt, htt⟩
                have htt' : toInt tt = (val3.val : ℤ) := htt hvhi
                have hadd : InRange lo hi (toInt res2 + toInt tt) := by
                  rw [hres2, htt', hfull hk1]
                  have hlo := hF.lo_le
                  have hp : (0 : ℤ) ≤ (decimal (↑s' : List U8) : ℤ) := by positivity
                  obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF _ (by have := hall'; rwa [hk1, List.take_length] at this) hDlt
                  constructor <;> omega
                step with hAdd res2 tt hadd as ⟨res3, hres3⟩
                refine ⟨by rw [hend1, hend], Or.inr ⟨by omega, ?_, ?_⟩, ?_⟩
                · have := hall'; rwa [hk1, List.take_length] at this
                · rw [hres3, hres2, htt']; exact hfull hk1
                · rw [hend1, hend, hstart1, hstart]; simp
    · -- second iteration: the range is exhausted, return
      rw [hstart, hend] at hnext
      simp only [lt_irrefl, ite_false] at hnext
      obtain ⟨rfl, _⟩ := hnext
      rcases hck : ch with _ | ⟨d, ct⟩ <;> rw [hck] at hH
      · step*
        exact final_unchecked hF hH hall res' hres'
      · step as ⟨o1, ho1⟩
        apply WP.spec_bind (final_checked hF hH hall res' hres' o1 ho1)
        intro r hr
        rw [WP.spec_ok]
        exact hr
  · exact ⟨rfl, by simp, Or.inl ⟨by simp, rfl, rfl, hres⟩⟩

end atoi_radix10
