import Proofs.Ref

/-!
`parse<T>` (`src/parse.rs`), generic over `T: FromStrRadixHelper`. The theorem is stated for
any instance that is *faithful* to an integer type with values `[lo, hi]`: its constants are
the ones `doit!` writes (`CHARS` digits, the first digit of the bound, the powers of ten) and
its arithmetic is the integers'. Each `doit!` instance is then shown faithful, and the
specification follows for that type.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- What `parse` promises: `str::parse` for the values `[lo, hi]`, read through `toInt`,
the error kinds matching core's up to `kindLike`. -/
def ParseSpec {T : Type} (inst : parse.FromStrRadixHelper T) (toInt : T → ℤ) (lo hi : ℤ) :
    Prop :=
  ∀ s : Slice U8, parse.parse inst s ⦃ (out : core.result.Result T ParseIntErrorPublic) =>
    match out with
    | .Ok v => stdParse lo hi s.val = .ok (toInt v)
    | .Err e => ∃ k, stdParse lo hi s.val = .error k ∧ kindLike e.kind k ⦄

/-- `v` is in `[lo, hi]`. -/
def InRange (lo hi v : ℤ) : Prop := lo ≤ v ∧ v ≤ hi

/-- A checked operation's answer: the value when the exact result `v` is in range, `none`
when it is not. -/
def CheckedIs (toInt : T → ℤ) (lo hi v : ℤ) : Option T → Prop
  | some z => InRange lo hi v ∧ toInt z = v
  | none => ¬ InRange lo hi v

/-- An instance of `FromStrRadixHelper` as `doit!` makes one for an integer type with values
`[lo, hi]`, `hi` having `c` digits; `toInt` reads a value. Every method succeeds, the
arithmetic is the integers' when the result is in range, and the checked arithmetic answers
`none` exactly when it is not. -/
structure Faithful {T : Type} (inst : parse.FromStrRadixHelper T) (toInt : T → ℤ)
    (lo hi : ℤ) (c : ℕ) : Prop where
  lo_le : lo ≤ 0
  hi_pos : 0 < hi
  signed : lo < 0 → lo = -(hi + 1)
  hi_lt : hi < 10 ^ c
  hi_ge : 10 ^ (c - 1) ≤ hi
  two_le_c : 2 ≤ c
  /-- The first significant digit times its weight fits (`hi + 1` is a power of two, so
  `10^(c-1)` never divides it). -/
  fs_mul_le : ((hi + 1) / 10 ^ (c - 1)) * 10 ^ (c - 1) ≤ hi
  range : ∀ x, InRange lo hi (toInt x)
  inj : ∀ x y, toInt x = toInt y → x = y
  MIN : inst.MIN ⦃ m => toInt m = lo ⦄
  CHARS : inst.CHARS ⦃ (n : Usize) => n.val = c ⦄
  FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (hi + 1) / 10 ^ (c - 1) ⦄
  TAIL : inst.TAIL ⦃ t => lo < 0 → toInt t = lo + ((hi + 1) / 10 ^ (c - 1)) * 10 ^ (c - 1) ⦄
  TREE : inst.TREE ⦃ (tr : Slice T) =>
    tr.val.length = c ∧ ∀ i (h : i < tr.val.length), toInt tr.val[i] = 10 ^ i ⦄
  BITS : inst.BITS ⦃ (b : U32) => 2 ^ b.val = hi - lo + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄
  from_u8 : ∀ u : U8, inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ hi → toInt t = u.val ⦄
  from_u16 : ∀ u : U16, inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ hi → toInt t = u.val ⦄
  from_u32 : ∀ u : U32, inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ hi → toInt t = u.val ⦄
  from_u64 : ∀ u : U64, inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ hi → toInt t = u.val ⦄
  from_u128 : ∀ u : U128, inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ hi → toInt t = u.val ⦄
  gt : ∀ x y, inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (toInt y < toInt x) ⦄
  add : ∀ x y, InRange lo hi (toInt x + toInt y) →
    inst.coreopsarithAddInst.add x y ⦃ z => toInt z = toInt x + toInt y ⦄
  sub : ∀ x y, InRange lo hi (toInt x - toInt y) →
    inst.coreopsarithSubInst.sub x y ⦃ z => toInt z = toInt x - toInt y ⦄
  mul : ∀ x y, InRange lo hi (toInt x * toInt y) →
    inst.coreopsarithMulInst.mul x y ⦃ z => toInt z = toInt x * toInt y ⦄
  add_checked : ∀ x y, inst.add_checked x y ⦃ r => CheckedIs toInt lo hi (toInt x + toInt y) r ⦄
  sub_checked : ∀ x y, inst.sub_checked x y ⦃ r => CheckedIs toInt lo hi (toInt x - toInt y) r ⦄
  mul_checked : ∀ x y, inst.mul_checked x y ⦃ r => CheckedIs toInt lo hi (toInt x * toInt y) r ⦄

/-! ### `u8`: the `doit!` instance is faithful

One lemma per method, then the record. A value is read as `(x.val : ℤ)`. -/

namespace U8F

abbrev inst := U8.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : U8) : InRange 0 255 (x.val : ℤ) := ⟨by omega, by scalar_tac⟩
theorem inj (x y : U8) (h : (x.val : ℤ) = (y.val : ℤ)) : x = y := UScalar.eq_of_val_eq (by omega)
theorem MIN : inst.MIN ⦃ m => (m.val : ℤ) = 0 ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 3 ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (255 + 1) / 10 ^ (3 - 1) ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (0 : ℤ) < 0 → (t.val : ℤ) = 0 + ((255 + 1) / 10 ^ (3 - 1)) * 10 ^ (3 - 1) ⦄ := by
  simp [WP.spec_ok]
theorem TREE :
    inst.TREE ⦃ (tr : Slice U8) =>
      tr.val.length = 3 ∧ ∀ i (h : i < tr.val.length), ((tr.val[i]).val : ℤ) = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [U8.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U8, Array.to_slice]
  · intro i h
    simp [U8.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U8, Array.to_slice] at h ⊢
    match i, h with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 255 - 0 + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.U8.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 255 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u8]
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 255 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u16, UScalar.cast_val_eq]; omega
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 255 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u32, UScalar.cast_val_eq]; omega
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 255 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u64, UScalar.cast_val_eq]; omega
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 255 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U8.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u128, UScalar.cast_val_eq]; omega
theorem gt (x y : U8) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide ((y.val : ℤ) < (x.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdU8.gt, liftFun2]
theorem add (x y : U8) (h : InRange 0 255 ((x.val : ℤ) + (y.val : ℤ))) :
    inst.coreopsarithAddInst.add x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithAddInst.add = U8.Insts.CoreOpsArithAddU8U8.add from rfl,
    U8.Insts.CoreOpsArithAddU8U8.add]
  exact WP.spec_mono (U8.add_spec (by rw [U8.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem sub (x y : U8) (h : InRange 0 255 ((x.val : ℤ) - (y.val : ℤ))) :
    inst.coreopsarithSubInst.sub x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) - (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = U8.Insts.CoreOpsArithSubU8U8.sub from rfl,
    U8.Insts.CoreOpsArithSubU8U8.sub]
  exact WP.spec_mono (U8.sub_spec (x := x) (y := y) (by have := h.1; omega)) fun z hz => by
    have hc := Nat.cast_sub (R := ℤ) hz.2; omega
theorem mul (x y : U8) (h : InRange 0 255 ((x.val : ℤ) * (y.val : ℤ))) :
    inst.coreopsarithMulInst.mul x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) * (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = U8.Insts.CoreOpsArithMulU8U8.mul from rfl,
    U8.Insts.CoreOpsArithMulU8U8.mul]
  exact WP.spec_mono (U8.mul_spec (by rw [U8.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem add_checked (x y : U8) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : U8 => (x.val : ℤ)) 0 255 ((x.val : ℤ) + (y.val : ℤ)) r ⦄ := by
  rw [show inst.add_checked = U8.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl,
    U8.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := U8.checked_add_bv_spec x y
  rw [U8.max_eq] at h
  cases hr : U8.checked_add x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : U8) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : U8 => (x.val : ℤ)) 0 255 ((x.val : ℤ) - (y.val : ℤ)) r ⦄ := by
  rw [show inst.sub_checked = U8.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl,
    U8.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := U8.checked_sub_bv_spec x y
  cases hr : U8.checked_sub x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange]
  · omega
  · have hc := Nat.cast_sub (R := ℤ) h.1
    have hx : x.val ≤ 255 := by scalar_tac
    omega
theorem mul_checked (x y : U8) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : U8 => (x.val : ℤ)) 0 255 ((x.val : ℤ) * (y.val : ℤ)) r ⦄ := by
  rw [show inst.mul_checked = U8.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl,
    U8.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := U8.checked_mul_bv_spec x y
  rw [U8.max_eq] at h
  cases hr : U8.checked_mul x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end U8F

theorem faithful_u8 : Faithful U8F.inst (fun x : U8 => (x.val : ℤ)) 0 255 3 :=
  { lo_le := le_refl 0, hi_pos := by norm_num, signed := fun h => absurd h (lt_irrefl 0)
    hi_lt := by norm_num, hi_ge := by norm_num, two_le_c := by norm_num, fs_mul_le := by norm_num
    range := U8F.range, inj := U8F.inj
    MIN := U8F.MIN, CHARS := U8F.CHARS, FIRST_SIG := U8F.FIRST_SIG, TAIL := U8F.TAIL
    TREE := U8F.TREE, BITS := U8F.BITS
    from_u8 := U8F.from_u8, from_u16 := U8F.from_u16, from_u32 := U8F.from_u32
    from_u64 := U8F.from_u64, from_u128 := U8F.from_u128, gt := U8F.gt
    add := U8F.add, sub := U8F.sub, mul := U8F.mul
    add_checked := U8F.add_checked, sub_checked := U8F.sub_checked, mul_checked := U8F.mul_checked }

end atoi_radix10
