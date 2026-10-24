import Proofs.Parse

/-!
The loops of `parse`, innermost first. Each lemma relates one extracted loop function to the
bytes of its slice, for any `Faithful` instance.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-! ### Bytes -/

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

theorem parse_loop1_loop0_spec {T : Type} {inst : parse.FromStrRadixHelper T} {toInt : T → ℤ}
    {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (s : Slice U8) (val : U8)
    (h0 : 0 < s.val.length) (hv : s.val[0]? = some val) :
    parse.parse_loop1_loop0 inst s val ⦃ (out : Slice U8 × U8 × Option (core.result.Result T ParseIntErrorPublic) ×
        Option (core.result.Result T ParseIntErrorPublic) × Bool) =>
      match out with
      | (s', v', r1, r2, b) =>
        match dropZeros s.val with
        | [] => (∃ t, r1 = some (.Ok t) ∧ toInt t = 0) ∧ r2 = none ∧ b = false
        | d :: rest => s'.val = d :: rest ∧ r1 = none ∧
            if isDigit d then r2 = none ∧ b = true ∧ v'.val = d.val - 48
            else r2 = some (.Err { kind := .Empty }) ∧ b = false ⦄ := by
  unfold parse.parse_loop1_loop0
  apply loop.spec_decr_nat (fun (p : Slice U8 × U8) => p.1.val.length)
    (fun (p : Slice U8 × U8) => 0 < p.1.val.length ∧ p.1.val[0]? = some p.2 ∧
      dropZeros p.1.val = dropZeros s.val)
  · rintro ⟨sl, v1⟩ ⟨h1, hv1, hd⟩
    simp only at h1 hv1 hd
    unfold parse.parse_loop1_loop0.body
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

theorem parse_loop0_loop0_loop1_spec {T : Type} {inst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c)
    (s : Slice U8) (is_signed_ty : Bool) (checked : Option (U8 × T)) (val val1 : U8) (l : Usize)
    (i : U8) (s1 s2 s3 s4 : Slice U8) (h0 : 0 < s.val.length) (hv : s.val[0]? = some val1) :
    parse.parse_loop0_loop0_loop1 inst s is_signed_ty checked val val1 l i s1 s2 s3 s4
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
  unfold parse.parse_loop0_loop0_loop1
  apply loop.spec_decr_nat (fun (p : Slice U8 × U8) => p.1.val.length)
    (fun (p : Slice U8 × U8) => 0 < p.1.val.length ∧ p.1.val[0]? = some p.2 ∧
      dropZeros p.1.val = dropZeros s.val)
  · rintro ⟨sl, v1⟩ ⟨h1, hv1, hd⟩
    simp only at h1 hv1 hd
    unfold parse.parse_loop0_loop0_loop1.body
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

end atoi_radix10
