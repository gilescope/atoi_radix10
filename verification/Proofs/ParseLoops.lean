import Proofs.Parse
import Proofs.StdDigits

/-!
The loops of `parse`, innermost first. Each lemma relates one extracted loop function to the
bytes of its slice, for any `Faithful` instance.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-! ### Bytes -/

theorem U8.val_lt_256 (b : U8) : b.val < 256 := by scalar_tac

/-- `b.wrapping_sub(b'0')` as a number. -/
theorem U8.wrapping_sub_48_val (b : U8) :
    (core.num.U8.wrapping_sub b 48#u8).val = (b.val + 256 - 48) % 256 := by
  have hb : b.val < 256 := by scalar_tac
  change (core.num.U8.wrapping_sub b 48#u8).bv.toNat = (b.bv.toNat + 256 - 48) % 256
  rw [core.num.U8.wrapping_sub_bv_eq, BitVec.toNat_sub]
  have h48 : (48#u8).bv.toNat = 48 := by decide
  rw [h48]
  change b.bv.toNat < 256 at hb
  omega

/-- The digit test on `b - b'0'` (wrapping): at most 9 exactly for the digits. -/
theorem wrapping_digit_test : ∀ b < 256, ((b + 256 - 48) % 256 ≤ 9 ↔ 48 ≤ b ∧ b ≤ 57) := by
  decide +kernel

/-- `<[T]>::first`. -/
@[step]
theorem core.slice.Slice.first_spec {T : Type} (s : Slice T) :
    core.slice.Slice.first s ⦃ o => o = s.val.head? ⦄ := by
  simp [core.slice.Slice.first, WP.spec_ok]

/-- The leading zeros stripped. -/
abbrev dropZeros (l : List U8) : List U8 := l.dropWhile fun b => decide (b = 48#u8)

theorem cons_of_getElem?_zero {a : U8} (l : List U8) (h : l[0]? = some a) : l = a :: l.tail := by
  cases l <;> simp_all

theorem dropZeros_drop_of_48 (l : List U8) (h : l[0]? = some 48#u8) :
    dropZeros l = dropZeros (l.drop 1) := by
  cases l <;> simp_all [dropZeros]

theorem dropZeros_of_ne {d : U8} (l : List U8) (h : l[0]? = some d) (hd : d ≠ 48#u8) :
    dropZeros l = l := by
  cases l <;> simp_all [dropZeros]

/-! ### The leading-zero loop

`src/parse.rs` lines 348-359: `val = b'0'; while val == b'0' { s = &s[1..]; val = match
s.first() { Some(v) => *v, None => return Ok(0) } }; val -= b'0'; if val > 9 { return
Err(Empty) }`. Entered with `val = s[0] = b'0'`. The lifted exits come back as the two `Option`s
(`Ok(0)`, `Err(Empty)`) and the flag says the loop fell through to the next digit. -/

theorem parse_inner_loop1_loop0_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (s : Slice U8) (val : U8)
    (h0 : 0 < s.val.length) (hv : s.val[0]? = some val) :
    parse.parse_inner_loop1_loop0 inst s val ⦃ (out : Slice U8 × U8 × Option (core.result.Result T ParseIntErrorPublic) ×
        Option (core.result.Result T ParseIntErrorPublic) × Bool) =>
      match out with
      | (s', v', r1, r2, b) =>
        match dropZeros s.val with
        | [] => (∃ t, r1 = some (.Ok t) ∧ toInt t = 0) ∧ r2 = none ∧ b = false
        | d :: rest => s'.val = d :: rest ∧ r1 = none ∧
            if isDigit d then r2 = none ∧ b = true ∧ v'.val = d.val - 48
            else r2 = some (.Err { kind := .Empty }) ∧ b = false ⦄ := by
  unfold parse.parse_inner_loop1_loop0
  apply loop.spec_decr_nat (fun (p : Slice U8 × U8) => p.1.val.length)
    (fun (p : Slice U8 × U8) => 0 < p.1.val.length ∧ p.1.val[0]? = some p.2 ∧
      dropZeros p.1.val = dropZeros s.val)
  · rintro ⟨sl, v1⟩ ⟨h1, hv1, hd⟩
    simp only at h1 hv1 hd
    unfold parse.parse_inner_loop1_loop0.body
    have hb : v1.val < 256 := by scalar_tac
    have hw := U8.wrapping_sub_48_val v1
    have hdig := wrapping_digit_test v1.val hb
    step*
    · -- all zeros: `return Ok(0)`
      have hv48 : v1 = 48#u8 := by assumption
      have ho : o = none := by assumption
      have h48 : (↑sl : List U8)[0]? = some 48#u8 := by rw [hv1, hv48]
      have hs1 : (↑s1 : List U8) = [] := by
        rw [← List.head?_eq_none_iff, ← o_post, ho]
      have hdz : dropZeros ↑s = [] := by
        rw [← hd, dropZeros_drop_of_48 _ h48, ← s1_post, hs1]; simp [dropZeros]
      apply WP.spec_bind (hF.from_u8 0#u8)
      intro t ht
      rw [WP.spec_ok, hdz]
      refine ⟨⟨t, rfl, ?_⟩, rfl, rfl⟩
      rw [ht (by simp; exact le_of_lt hF.hi_pos)]; simp
    · -- another zero: next iteration
      have hv48 : v1 = 48#u8 := by assumption
      have h48 : (↑sl : List U8)[0]? = some 48#u8 := by rw [hv1, hv48]
      have hhead : (↑s1 : List U8).head? = some val2 := by rwa [← o_post]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hl : (↑s1 : List U8) with _ | ⟨a, l⟩
        · simp [hl] at hhead
        · simp
      · rcases hl : (↑s1 : List U8) with _ | ⟨a, l⟩
        · simp [hl] at hhead
        · simpa [hl] using hhead
      · rw [← hd, dropZeros_drop_of_48 _ h48, ← s1_post]
      · rw [s1_post]; simp; omega
    · -- a byte that is not a digit: `Err(Empty)`
      have hne : ¬ v1 = 48#u8 := by assumption
      have hgt : val1 > 9#u8 := by assumption
      have hcons := cons_of_getElem?_zero _ hv1
      have hdz : dropZeros ↑s = v1 :: (↑sl : List U8).tail := by
        rw [← hd, dropZeros_of_ne _ hv1 hne]; exact hcons
      have h9 : (9#u8).val < val1.val := hgt
      have h9v : (9#u8).val = 9 := by decide +kernel
      rw [h9v, val1_post, hw] at h9
      have hnd : ¬ isDigit v1 := by show ¬ (48 ≤ v1.val ∧ v1.val ≤ 57); omega
      simp only [hdz, hnd, ite_false]
      first | exact hcons | trivial
    · -- a digit: fall through with its value
      have hne : ¬ v1 = 48#u8 := by assumption
      have hle : ¬ val1 > 9#u8 := by assumption
      have hcons := cons_of_getElem?_zero _ hv1
      have hdz : dropZeros ↑s = v1 :: (↑sl : List U8).tail := by
        rw [← hd, dropZeros_of_ne _ hv1 hne]; exact hcons
      have h9 : ¬ (9#u8).val < val1.val := hle
      have h9v : (9#u8).val = 9 := by decide +kernel
      rw [h9v, val1_post, hw] at h9
      have hdg : isDigit v1 := by show 48 ≤ v1.val ∧ v1.val ≤ 57; omega
      have hval : val1.val = v1.val - 48 := by rw [val1_post, hw]; omega
      simp only [hdz, hdg, ite_true]
      exact ⟨hcons, hval⟩
  · exact ⟨h0, hv, rfl⟩

/-! ### The leading-zero loop of the negative path

`src/parse.rs` lines 516-522, the same `while val == b'0'` loop without the digit check after
it: the loop returns to the top of the outer `loop`. The other variables ride through. -/

theorem parse_inner_loop0_loop0_loop1_spec {T : Type} {inst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c)
    (s : Slice U8) (is_signed_ty : Bool) (checked : Option (U8 × T)) (val val1 : U8) (l : Usize)
    (i : U8) (s1 s2 s3 s4 : Slice U8) (h0 : 0 < s.val.length) (hv : s.val[0]? = some val1) :
    parse.parse_inner_loop0_loop0_loop1 inst s is_signed_ty checked val val1 l i s1 s2 s3 s4
      ⦃ (out : Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Usize ×
          Option (core.result.Result T ParseIntErrorPublic) × U8 × Slice U8 × Slice U8 × Slice U8 ×
          Slice U8) =>
      match out with
      | (s', b', ch', v', v1', l', r, i', t1, t2, t3, t4) =>
        b' = is_signed_ty ∧ ch' = checked ∧ v' = val ∧ l' = l ∧ i' = i ∧
        t1 = s1 ∧ t2 = s2 ∧ t3 = s3 ∧ t4 = s4 ∧
        match dropZeros s.val with
        | [] => ∃ t, r = some (.Ok t) ∧ toInt t = 0
        | d :: rest => s'.val = d :: rest ∧ r = none ∧ v1' = d ⦄ := by
  unfold parse.parse_inner_loop0_loop0_loop1
  apply loop.spec_decr_nat (fun (p : Slice U8 × U8) => p.1.val.length)
    (fun (p : Slice U8 × U8) => 0 < p.1.val.length ∧ p.1.val[0]? = some p.2 ∧
      dropZeros p.1.val = dropZeros s.val)
  · rintro ⟨sl, v1⟩ ⟨h1, hv1, hd⟩
    simp only at h1 hv1 hd
    unfold parse.parse_inner_loop0_loop0_loop1.body
    step*
    · -- all zeros: `return Ok(0)`
      have hv48 : v1 = 48#u8 := by assumption
      have ho : o = none := by assumption
      have h48 : (↑sl : List U8)[0]? = some 48#u8 := by rw [hv1, hv48]
      have hs5 : (↑s5 : List U8) = [] := by
        rw [← List.head?_eq_none_iff, ← o_post, ho]
      have hdz : dropZeros ↑s = [] := by
        rw [← hd, dropZeros_drop_of_48 _ h48, ← s5_post, hs5]; simp [dropZeros]
      apply WP.spec_bind (hF.from_u8 0#u8)
      intro t ht
      rw [WP.spec_ok, hdz]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, t, rfl, ?_⟩
      rw [ht (by simp; exact le_of_lt hF.hi_pos)]; simp
    · -- another zero: next iteration
      have hv48 : v1 = 48#u8 := by assumption
      have h48 : (↑sl : List U8)[0]? = some 48#u8 := by rw [hv1, hv48]
      have hhead : (↑s5 : List U8).head? = some val2 := by rwa [← o_post]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hl : (↑s5 : List U8) with _ | ⟨a, l⟩
        · simp [hl] at hhead
        · simp
      · rcases hl : (↑s5 : List U8) with _ | ⟨a, l⟩
        · simp [hl] at hhead
        · simpa [hl] using hhead
      · rw [← hd, dropZeros_drop_of_48 _ h48, ← s5_post]
      · rw [s5_post]; simp; omega
    · -- a byte that is not `'0'`: back to the top
      have hne : ¬ v1 = 48#u8 := by assumption
      have hcons := cons_of_getElem?_zero _ hv1
      have hdz : dropZeros ↑s = v1 :: (↑sl : List U8).tail := by
        rw [← hd, dropZeros_of_ne _ hv1 hne]; exact hcons
      simp only [hdz]
      exact ⟨hcons, trivial⟩
  · exact ⟨h0, hv, rfl⟩

/-! ### The positive pre-pass

`src/parse.rs` lines 199-364, the `loop` around the SWAR block: when the slice is shorter than
`CHARS` digits it falls through to the block; when it is exactly `CHARS` long and starts with a
small enough digit, that digit is set aside in `checked` (with its weight) and the rest goes to
the block; leading zeros are stripped; anything else is a positive overflow. -/

/-- What the pre-pass maintains, and hands over: the slice is non-empty and starts with the digit
`val1` stands for; some accumulator `a` (zero unless a digit was set aside) already accounts for
the bytes consumed, so folding the rest from `a` is folding the original from zero; no proper
prefix of the rest can overflow from `a`; and `checked`, when set, is `a` at its weight. -/
structure PreInv {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (c : ℕ) (D0 : List U8) (s : Slice U8)
    (checked : Option (U8 × T)) (val1 : U8) : Prop where
  len_pos : 0 < s.val.length
  head : ∃ d, s.val[0]? = some d ∧ isDigit d ∧ val1.val = d.val - 48
  acc : ∃ a : ℤ, 0 ≤ a ∧ a ≤ hi ∧
    stdDigits lo hi false 0 D0 = stdDigits lo hi false a s.val ∧
    (∀ k, k < s.val.length → k + 1 < c → a * 10 ^ k + (10 ^ k - 1) ≤ hi) ∧
    (checked = none → a = 0) ∧
    (∀ d t, checked = some (d, t) → toInt t = a * 10 ^ s.val.length ∧ s.val.length + 1 = c)

/-- The result of the whole positive path, against the reference. -/
def PosResult {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) :
    core.result.Result T ParseIntErrorPublic → Prop
  | .Ok t => stdDigits lo hi false 0 D0 = .ok (toInt t)
  | .Err e => ∃ k, stdDigits lo hi false 0 D0 = .error k ∧ kindLike e.kind k

/-- The pre-pass's overflow verdict is right: a first digit with too many digits behind it, or
one too big for a slice of exactly `CHARS` digits, cannot fold into range. -/
theorem pre_overflow {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (D0 : List U8) (s : Slice U8) (d : U8)
    (hdd : isDigit d) (hcons : (↑s : List U8) = d :: (↑s : List U8).tail)
    (hfold : stdDigits lo hi false 0 D0 = stdDigits lo hi false 0 s.val)
    (hd1 : 1 ≤ (d.val : ℤ) - 48)
    (hbig : c ≤ s.val.length - 1 ∨ (s.val.length = c ∧ (hi + 1) / 10 ^ (c - 1) < (d.val : ℤ) - 48)) :
    PosResult toInt lo hi D0 (.Err { kind := .PosOverflow }) := by
  have hc2 := hF.three_le_c
  have hlo := hF.lo_le
  have hhi9 : (9 : ℤ) ≤ hi := by
    have := hF.hi_ge
    have : (10 : ℤ) ^ 1 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hd9 := digit_sub48_le9 hdd
  have hr : lo ≤ 0 * 10 + ((d.val : ℤ) - 48) ∧ 0 * 10 + ((d.val : ℤ) - 48) ≤ hi := ⟨by omega, by omega⟩
  have hstep : stdDigits lo hi false 0 s.val = stdDigits lo hi false ((d.val : ℤ) - 48) (↑s : List U8).tail := by
    rw [hcons, stdDigits_cons_digit lo hi 0 d _ hdd hr]; simp
  have htail : (↑s : List U8).tail.length = s.val.length - 1 := by simp
  have hne : (↑s : List U8).tail ≠ [] := by
    intro h; rw [h] at htail; simp at htail
    rcases hbig with h1 | ⟨h1, _⟩ <;> omega
  obtain ⟨k, hk⟩ : ∃ k, stdDigits lo hi false ((d.val : ℤ) - 48) (↑s : List U8).tail = .error k := by
    rcases hbig with h1 | ⟨h1, h2⟩
    · exact stdDigits_long_err lo hi _ c _ hd1 (by have := hF.hi_lt; omega) (by omega) (by omega)
    · apply stdDigits_err_of_big lo hi _ _ (by omega) _ hne
      rw [htail, h1]
      have hfl := fs_floor hi c
      have hp : (0 : ℤ) ≤ 10 ^ (c - 1) := by positivity
      nlinarith
  refine ⟨k, by rw [hfold, hstep, hk], ?_⟩
  rcases stdDigits_pos_err_kinds lo hi _ _ k hk with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

theorem parse_inner_loop1_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (s0 : Slice U8) (is_signed_ty : Bool)
    (checked : Option (U8 × T)) (val val1 : U8) (s1 s2 : Slice U8)
    (h : PreInv toInt lo hi c s0.val s0 checked val1) :
    parse.parse_inner_loop1 inst s0 is_signed_ty checked val val1 s1 s2
      ⦃ (out : Slice U8 × Bool × Option (U8 × T) × U8 × U8 ×
          Option (core.result.Result T ParseIntErrorPublic) × Slice U8 × Slice U8) =>
      match out with
      | (s', b', ch', v', v1', r, t1, t2) =>
        b' = is_signed_ty ∧ v' = val ∧ t1 = s1 ∧ t2 = s2 ∧
        match r with
        | none => PreInv toInt lo hi c s0.val s' ch' v1' ∧ s'.val.length < c
        | some r => PosResult toInt lo hi s0.val r ⦄ := by
  unfold parse.parse_inner_loop1
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Slice U8 × Slice U8) => p.1.val.length)
    (fun (p : Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Slice U8 × Slice U8) =>
      match p with
      | (s, b, ch, v, v1, t1, t2) =>
        b = is_signed_ty ∧ v = val ∧ t1 = s1 ∧ t2 = s2 ∧ PreInv toInt lo hi c s0.val s ch v1)
  · rintro ⟨s, b, ch, v, v1, t1, t2⟩ ⟨rfl, rfl, rfl, rfl, hinv⟩
    have hinv0 := hinv
    obtain ⟨hlen, ⟨d, hd0, hdd, hv1⟩, a, ha0, hahi, hfold, hbnd, hnone, hsome⟩ := hinv
    have hc2 := hF.three_le_c
    have hC := hF.CHARS
    have hFS := hF.FIRST_SIG
    have hTR := hF.TREE
    have hF8 := hF.from_u8
    have hMul := hF.mul
    unfold parse.parse_inner_loop1.body
    have hlo := hF.lo_le
    have hhi9 : (9 : ℤ) ≤ hi := by
      have := hF.hi_ge
      have : (10 : ℤ) ^ 1 ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hd9 := digit_sub48_le9 hdd
    have hcons := cons_of_getElem?_zero _ hd0
    have h48v : (48#u8).val = 48 := by simp
    have h0v : (0#u8).val = 0 := by simp
    have hv1d : (v1.val : ℤ) = (d.val : ℤ) - 48 := by have := hdd.1; omega
    have h48 : v1 = 0#u8 → (↑s : List U8)[0]? = some 48#u8 := by
      intro h0
      have hv0 : v1.val = 0 := by rw [h0, h0v]
      have : d = 48#u8 := by apply UScalar.eq_of_val_eq; have := hdd.1; omega
      rw [hd0, this]
    have hv1hi : (v1.val : ℤ) ≤ hi := by omega
    -- `checked` is unset while the slice is at least `CHARS` long
    have hch : c ≤ s.val.length → ch = none ∧ a = 0 := by
      intro hge
      rcases hc : ch with _ | ⟨d2, t2'⟩
      · exact ⟨rfl, hnone hc⟩
      · exfalso; have := (hsome d2 t2' hc).2; omega
    step*
    split
    · -- the slice is exactly CHARS long
      rename_i hlc
      have hslen : s.val.length = c := by
        have := congrArg UScalar.val hlc; rw [Slice.len_val] at this; simp [Slice.length] at this; omega
      obtain ⟨hchn, ha⟩ := hch (le_of_eq hslen.symm)
      subst ha
      step as ⟨fs, hfs⟩
      split
      · -- a small first digit: set it aside with its weight
        rename_i hle
        have hle' : (v1.val : ℤ) ≤ (hi + 1) / 10 ^ (c - 1) := by
          have := UScalar.le_equiv v1 fs |>.mp hle; omega
        step as ⟨vt, hvt⟩
        step as ⟨tr, htrlen, htr⟩
        step as ⟨i2, hi2⟩
        step as ⟨t, ht⟩
        have hi2c : i2.val = c - 1 := by omega
        have htv : toInt t = 10 ^ (c - 1) := by
          rw [ht]; simp only [hi2c]; exact htr (c - 1) (by omega)
        have hvtv : toInt vt = (v1.val : ℤ) := hvt hv1hi
        have hmulr : InRange lo hi (toInt vt * toInt t) := by
          rw [hvtv, htv]
          have hp : (0 : ℤ) ≤ 10 ^ (c - 1) := by positivity
          have hp0 : (0 : ℤ) ≤ (v1.val : ℤ) * 10 ^ (c - 1) := by positivity
          have := hF.fs_mul_le
          refine ⟨by omega, ?_⟩
          nlinarith
        step with hMul vt t hmulr as ⟨mult, hmult⟩
        step as ⟨vn, hvn⟩
        step as ⟨val2, hval2⟩
        step as ⟨s5, hs5, hs5len⟩
        have hvnd : (↑s : List U8)[1]? = some vn := by
          rw [hvn]; exact List.getElem?_eq_getElem _
        have hw := U8.wrapping_sub_48_val vn
        have hvnb : vn.val < 256 := U8.val_lt_256 vn
        have hdig := wrapping_digit_test vn.val hvnb
        have hs5cons : (↑s5 : List U8) = vn :: (↑s5 : List U8).tail := by
          apply cons_of_getElem?_zero
          rw [hs5]; simp; exact hvnd
        have hfold' : stdDigits lo hi false 0 (↑s0 : List U8) =
            stdDigits lo hi false ((v1.val : ℤ)) (↑s5 : List U8) := by
          rw [hfold, hcons, stdDigits_cons_digit lo hi 0 d _ hdd ⟨by omega, by omega⟩, hs5]
          simp [hv1d]
        step
        split
        · -- the next byte is not a digit
          rename_i hgt9
          have h9 : 9 < val2.val := by have := UScalar.lt_equiv 9#u8 val2 |>.mp hgt9; simpa using this
          rw [hval2, hw] at h9
          have hnd : ¬ isDigit vn := by show ¬ (48 ≤ vn.val ∧ vn.val ≤ 57); omega
          have hres : stdDigits lo hi false 0 (↑s0 : List U8) = .error .InvalidDigit := by
            rw [hfold', hs5cons, stdDigits_nonDigit lo hi false _ vn _ hnd]
          step*
          exact ⟨.InvalidDigit, hres, Or.inl rfl⟩
        · -- a digit: continue, the first digit set aside
          rename_i hle9
          have h9 : val2.val ≤ 9 := by
            have := mt (UScalar.lt_equiv 9#u8 val2).mpr hle9; simp at this; omega
          rw [hval2, hw] at h9
          have hdg : isDigit vn := by show 48 ≤ vn.val ∧ vn.val ≤ 57; omega
          have hs5l : (↑s5 : List U8).length = c - 1 := by rw [hs5]; simp; omega
          have hpre : PreInv toInt lo hi c (↑s0) s5 (some (v1, mult)) val2 := by
            refine ⟨?_, ⟨vn, ?_, hdg, ?_⟩, (v1.val : ℤ), by omega, by omega, hfold', ?_, ?_, ?_⟩
            · rw [hs5]; simp; omega
            · rw [hs5]; simp; exact hvnd
            · rw [hval2, hw]; omega
            · intro k hk _
              rw [hs5l] at hk
              have hfs9 := fs_le_9 hi c (by have := hF.hi_lt; omega) (by omega) hF.fs_mul_le
              have hp : (0 : ℤ) ≤ 10 ^ k := by positivity
              have hk1 : (10 : ℤ) ^ (k + 1) ≤ 10 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
              have := hF.hi_ge
              rw [pow_succ] at hk1
              nlinarith
            · intro h; cases h
            · intro d' t' h
              cases h
              refine ⟨?_, by omega⟩
              rw [hmult, hvtv, htv, hs5l]
          have hlt : (↑s5 : List U8).length < (↑s : List U8).length := by omega
          step*
      · -- too big a first digit: overflow
        rename_i hgt
        have hgt' : (hi + 1) / 10 ^ (c - 1) < (v1.val : ℤ) := by
          have := mt (UScalar.le_equiv v1 fs).mpr hgt; simp at this; omega
        step*
        have hv0 : ¬ v1 = 0#u8 := by assumption
        have hv0' : v1.val ≠ 0 := fun h => hv0 (UScalar.eq_of_val_eq (by rw [h, h0v]))
        exact pre_overflow hF _ s d hdd hcons hfold (by omega) (Or.inr ⟨hslen, by omega⟩)
    · -- longer than CHARS
      rename_i hne
      have hslen : c < s.val.length := by
        have h1 : ¬ s.val.length < c := by
          intro hlt; apply ‹¬ s.len < i›
          rw [UScalar.lt_equiv, Slice.len_val]; simp [Slice.length]; omega
        have h2 : s.val.length ≠ c := by
          intro heq; apply hne; apply UScalar.eq_of_val_eq; rw [Slice.len_val]; simp [Slice.length]; omega
        omega
      obtain ⟨hchn, ha⟩ := hch (by omega)
      subst ha
      step*
      · -- leading zero: strip the zeros
        have hv0 : v1 = 0#u8 := by assumption
        step with parse_inner_loop1_loop0_spec hF s 48#u8 hlen (h48 hv0) as ⟨s4, val2, lr, lr1, le, hpost⟩
        rcases hdz : dropZeros ↑s with _ | ⟨d', rest⟩ <;> simp only [hdz] at hpost
        · -- all zeros
          obtain ⟨⟨t, hlr, ht⟩, hlr1, hle⟩ := hpost
          subst hlr
          have hres : stdDigits lo hi false 0 (↑s0 : List U8) = .ok (toInt t) := by
            rw [hfold, ht]
            exact stdDigits_zeros lo hi _ hlo (by omega) hdz
          step*
          exact hres
        · obtain ⟨hs4, hlr, hrest⟩ := hpost
          subst hlr
          have hdz' : (↑s : List U8).dropWhile (fun b => decide (b = 48#u8)) = d' :: rest := hdz
          split_ifs at hrest with hdg
          · -- a digit after the zeros: next iteration
            obtain ⟨hlr1, hle, hval2⟩ := hrest
            subst hlr1 hle
            have hfold' : stdDigits lo hi false 0 (↑s0 : List U8) = stdDigits lo hi false 0 (↑s4 : List U8) := by
              rw [hfold, stdDigits_dropZeros lo hi _ hlo (by omega), hdz', hs4]
            have hlt : (↑s4 : List U8).length < (↑s : List U8).length := by
              rw [hs4, ← hdz]
              have h1 := dropZeros_drop_of_48 _ (h48 hv0)
              rw [h1]
              calc (dropZeros (List.drop 1 ↑s)).length ≤ (List.drop 1 (↑s : List U8)).length :=
                    (List.dropWhile_sublist _).length_le
                _ < (↑s : List U8).length := by simp; omega
            have hpre : PreInv toInt lo hi c (↑s0) s4 ch val2 := by
              refine ⟨by rw [hs4]; simp, ⟨d', by rw [hs4]; simp, hdg, hval2⟩, 0, le_refl 0, by omega, hfold', ?_, fun _ => rfl, ?_⟩
              · intro k hk hkc; exact hbnd k (by omega) hkc
              · intro d2 t2' h; rw [hchn] at h; cases h
            step*
          · -- a non-digit after the zeros: `Err(Empty)`, where core says bad digit
            obtain ⟨hlr1, hle⟩ := hrest
            subst hlr1
            have hres : stdDigits lo hi false 0 (↑s0 : List U8) = .error .InvalidDigit := by
              rw [hfold, stdDigits_dropZeros lo hi _ hlo (by omega), hdz',
                stdDigits_nonDigit lo hi false 0 d' rest hdg]
            step*
            exact ⟨.InvalidDigit, hres, Or.inr rfl⟩
      · -- a first digit with too many behind it: overflow
        have hv0 : ¬ v1 = 0#u8 := by assumption
        have hv0' : v1.val ≠ 0 := fun h => hv0 (UScalar.eq_of_val_eq (by rw [h, h0v]))
        exact pre_overflow hF _ s d hdd hcons hfold (by omega) (Or.inl (by omega))
  · exact ⟨rfl, rfl, rfl, rfl, h⟩

end atoi_radix10
