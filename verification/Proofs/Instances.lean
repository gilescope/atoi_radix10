import Proofs.Kind
import Mathlib.Tactic.IntervalCases

/-!
`Faithful` for the other nine integer types, each the `u8` record again with its constants, and
the `parse` theorem for each. Values are read as `x.val`: a natural for the unsigned types, an
integer for the signed ones.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-! ### `u16` -/

namespace U16F

abbrev inst := U16.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : U16) : InRange 0 65535 (x.val : ℤ) := ⟨by omega, by scalar_tac⟩
theorem inj (x y : U16) (h : (x.val : ℤ) = (y.val : ℤ)) : x = y := UScalar.eq_of_val_eq (by omega)
theorem MIN : inst.MIN ⦃ m => (m.val : ℤ) = 0 ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 5 ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (65535 + 1) / 10 ^ (5 - 1) ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (0 : ℤ) < 0 → (t.val : ℤ) = 0 + ((65535 + 1) / 10 ^ (5 - 1)) * 10 ^ (5 - 1) ⦄ := by
  simp [WP.spec_ok]
theorem TREE :
    inst.TREE ⦃ (tr : Slice U16) =>
      tr.val.length = 5 ∧ ∀ i (h : i < tr.val.length), ((tr.val[i]).val : ℤ) = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [U16.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U16, Array.to_slice]
  · intro i h
    simp [U16.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U16, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 65535 - 0 + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.U16.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 65535 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u8, UScalar.cast_val_eq]; omega
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 65535 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u16]
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 65535 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u32, UScalar.cast_val_eq]; omega
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 65535 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u64, UScalar.cast_val_eq]; omega
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 65535 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u128, UScalar.cast_val_eq]; omega
theorem gt (x y : U16) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide ((y.val : ℤ) < (x.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdU16.gt, liftFun2]
theorem eq (x y : U16) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide ((x.val : ℤ) = (y.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqU16.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact UScalar.eq_of_val_eq (by omega)
theorem add (x y : U16) (h : InRange 0 65535 ((x.val : ℤ) + (y.val : ℤ))) :
    inst.coreopsarithAddInst.add x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithAddInst.add = U16.Insts.CoreOpsArithAddU16U16.add from rfl,
    U16.Insts.CoreOpsArithAddU16U16.add]
  exact WP.spec_mono (U16.add_spec (by rw [U16.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem sub (x y : U16) (h : InRange 0 65535 ((x.val : ℤ) - (y.val : ℤ))) :
    inst.coreopsarithSubInst.sub x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) - (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = U16.Insts.CoreOpsArithSubU16U16.sub from rfl,
    U16.Insts.CoreOpsArithSubU16U16.sub]
  exact WP.spec_mono (U16.sub_spec (x := x) (y := y) (by have := h.1; omega)) fun z hz => by
    have hc := Nat.cast_sub (R := ℤ) hz.2; omega
theorem mul (x y : U16) (h : InRange 0 65535 ((x.val : ℤ) * (y.val : ℤ))) :
    inst.coreopsarithMulInst.mul x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) * (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = U16.Insts.CoreOpsArithMulU16U16.mul from rfl,
    U16.Insts.CoreOpsArithMulU16U16.mul]
  exact WP.spec_mono (U16.mul_spec (by rw [U16.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem add_checked (x y : U16) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : U16 => (x.val : ℤ)) 0 65535 ((x.val : ℤ) + (y.val : ℤ)) r ⦄ := by
  rw [show inst.add_checked = U16.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := U16.checked_add_bv_spec x y
  rw [U16.max_eq] at h
  cases hr : U16.checked_add x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : U16) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : U16 => (x.val : ℤ)) 0 65535 ((x.val : ℤ) - (y.val : ℤ)) r ⦄ := by
  rw [show inst.sub_checked = U16.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := U16.checked_sub_bv_spec x y
  cases hr : U16.checked_sub x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange]
  · omega
  · have hc := Nat.cast_sub (R := ℤ) h.1
    have hx : x.val ≤ 65535 := by scalar_tac
    omega
theorem mul_checked (x y : U16) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : U16 => (x.val : ℤ)) 0 65535 ((x.val : ℤ) * (y.val : ℤ)) r ⦄ := by
  rw [show inst.mul_checked = U16.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, U16.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := U16.checked_mul_bv_spec x y
  rw [U16.max_eq] at h
  cases hr : U16.checked_mul x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end U16F

theorem faithful_u16 : Faithful U16F.inst (fun x : U16 => (x.val : ℤ)) 0 65535 5 :=
  { lo_le := le_refl 0, hi_pos := by norm_num, signed := fun h => absurd h (lt_irrefl 0)
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := U16F.range, inj := U16F.inj
    MIN := U16F.MIN, CHARS := U16F.CHARS, FIRST_SIG := U16F.FIRST_SIG, TAIL := U16F.TAIL
    TREE := U16F.TREE, BITS := U16F.BITS
    from_u8 := U16F.from_u8, from_u16 := U16F.from_u16, from_u32 := U16F.from_u32
    from_u64 := U16F.from_u64, from_u128 := U16F.from_u128, gt := U16F.gt, eq := U16F.eq
    add := U16F.add, sub := U16F.sub, mul := U16F.mul
    add_checked := U16F.add_checked, sub_checked := U16F.sub_checked, mul_checked := U16F.mul_checked }

/-- `parse::<u16>` meets core's `str::parse::<u16>`. -/
theorem parse_spec_u16 : ParseSpec U16F.inst (fun x : U16 => (x.val : ℤ)) 0 65535 :=
  parse_spec faithful_u16

/-! ### `u32` -/

namespace U32F

abbrev inst := U32.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : U32) : InRange 0 4294967295 (x.val : ℤ) := ⟨by omega, by scalar_tac⟩
theorem inj (x y : U32) (h : (x.val : ℤ) = (y.val : ℤ)) : x = y := UScalar.eq_of_val_eq (by omega)
theorem MIN : inst.MIN ⦃ m => (m.val : ℤ) = 0 ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 10 ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (4294967295 + 1) / 10 ^ (10 - 1) ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (0 : ℤ) < 0 → (t.val : ℤ) = 0 + ((4294967295 + 1) / 10 ^ (10 - 1)) * 10 ^ (10 - 1) ⦄ := by
  simp [WP.spec_ok]
theorem TREE :
    inst.TREE ⦃ (tr : Slice U32) =>
      tr.val.length = 10 ∧ ∀ i (h : i < tr.val.length), ((tr.val[i]).val : ℤ) = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [U32.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U32, Array.to_slice]
  · intro i h
    simp [U32.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U32, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 4294967295 - 0 + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.U32.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 4294967295 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u8, UScalar.cast_val_eq]; omega
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 4294967295 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u16, UScalar.cast_val_eq]; omega
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 4294967295 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u32]
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 4294967295 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u64, UScalar.cast_val_eq]; omega
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 4294967295 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u128, UScalar.cast_val_eq]; omega
theorem gt (x y : U32) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide ((y.val : ℤ) < (x.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdU32.gt, liftFun2]
theorem eq (x y : U32) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide ((x.val : ℤ) = (y.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqU32.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact UScalar.eq_of_val_eq (by omega)
theorem add (x y : U32) (h : InRange 0 4294967295 ((x.val : ℤ) + (y.val : ℤ))) :
    inst.coreopsarithAddInst.add x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithAddInst.add = U32.Insts.CoreOpsArithAddU32U32.add from rfl,
    U32.Insts.CoreOpsArithAddU32U32.add]
  exact WP.spec_mono (U32.add_spec (by rw [U32.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem sub (x y : U32) (h : InRange 0 4294967295 ((x.val : ℤ) - (y.val : ℤ))) :
    inst.coreopsarithSubInst.sub x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) - (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = U32.Insts.CoreOpsArithSubU32U32.sub from rfl,
    U32.Insts.CoreOpsArithSubU32U32.sub]
  exact WP.spec_mono (U32.sub_spec (x := x) (y := y) (by have := h.1; omega)) fun z hz => by
    have hc := Nat.cast_sub (R := ℤ) hz.2; omega
theorem mul (x y : U32) (h : InRange 0 4294967295 ((x.val : ℤ) * (y.val : ℤ))) :
    inst.coreopsarithMulInst.mul x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) * (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = U32.Insts.CoreOpsArithMulU32U32.mul from rfl,
    U32.Insts.CoreOpsArithMulU32U32.mul]
  exact WP.spec_mono (U32.mul_spec (by rw [U32.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem add_checked (x y : U32) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : U32 => (x.val : ℤ)) 0 4294967295 ((x.val : ℤ) + (y.val : ℤ)) r ⦄ := by
  rw [show inst.add_checked = U32.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := U32.checked_add_bv_spec x y
  rw [U32.max_eq] at h
  cases hr : U32.checked_add x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : U32) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : U32 => (x.val : ℤ)) 0 4294967295 ((x.val : ℤ) - (y.val : ℤ)) r ⦄ := by
  rw [show inst.sub_checked = U32.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := U32.checked_sub_bv_spec x y
  cases hr : U32.checked_sub x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange]
  · omega
  · have hc := Nat.cast_sub (R := ℤ) h.1
    have hx : x.val ≤ 4294967295 := by scalar_tac
    omega
theorem mul_checked (x y : U32) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : U32 => (x.val : ℤ)) 0 4294967295 ((x.val : ℤ) * (y.val : ℤ)) r ⦄ := by
  rw [show inst.mul_checked = U32.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, U32.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := U32.checked_mul_bv_spec x y
  rw [U32.max_eq] at h
  cases hr : U32.checked_mul x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end U32F

theorem faithful_u32 : Faithful U32F.inst (fun x : U32 => (x.val : ℤ)) 0 4294967295 10 :=
  { lo_le := le_refl 0, hi_pos := by norm_num, signed := fun h => absurd h (lt_irrefl 0)
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := U32F.range, inj := U32F.inj
    MIN := U32F.MIN, CHARS := U32F.CHARS, FIRST_SIG := U32F.FIRST_SIG, TAIL := U32F.TAIL
    TREE := U32F.TREE, BITS := U32F.BITS
    from_u8 := U32F.from_u8, from_u16 := U32F.from_u16, from_u32 := U32F.from_u32
    from_u64 := U32F.from_u64, from_u128 := U32F.from_u128, gt := U32F.gt, eq := U32F.eq
    add := U32F.add, sub := U32F.sub, mul := U32F.mul
    add_checked := U32F.add_checked, sub_checked := U32F.sub_checked, mul_checked := U32F.mul_checked }

/-- `parse::<u32>` meets core's `str::parse::<u32>`. -/
theorem parse_spec_u32 : ParseSpec U32F.inst (fun x : U32 => (x.val : ℤ)) 0 4294967295 :=
  parse_spec faithful_u32

/-! ### `u64` -/

namespace U64F

abbrev inst := U64.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : U64) : InRange 0 18446744073709551615 (x.val : ℤ) := ⟨by omega, by scalar_tac⟩
theorem inj (x y : U64) (h : (x.val : ℤ) = (y.val : ℤ)) : x = y := UScalar.eq_of_val_eq (by omega)
theorem MIN : inst.MIN ⦃ m => (m.val : ℤ) = 0 ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 20 ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (18446744073709551615 + 1) / 10 ^ (20 - 1) ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (0 : ℤ) < 0 → (t.val : ℤ) = 0 + ((18446744073709551615 + 1) / 10 ^ (20 - 1)) * 10 ^ (20 - 1) ⦄ := by
  simp [WP.spec_ok]
theorem TREE :
    inst.TREE ⦃ (tr : Slice U64) =>
      tr.val.length = 20 ∧ ∀ i (h : i < tr.val.length), ((tr.val[i]).val : ℤ) = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [U64.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U64, Array.to_slice]
  · intro i h
    simp [U64.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U64, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 18446744073709551615 - 0 + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.U64.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 18446744073709551615 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u8, UScalar.cast_val_eq]; omega
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 18446744073709551615 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u16, UScalar.cast_val_eq]; omega
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 18446744073709551615 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u32, UScalar.cast_val_eq]; omega
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 18446744073709551615 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u64]
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 18446744073709551615 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u128, UScalar.cast_val_eq]; omega
theorem gt (x y : U64) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide ((y.val : ℤ) < (x.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdU64.gt, liftFun2]
theorem eq (x y : U64) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide ((x.val : ℤ) = (y.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqU64.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact UScalar.eq_of_val_eq (by omega)
theorem add (x y : U64) (h : InRange 0 18446744073709551615 ((x.val : ℤ) + (y.val : ℤ))) :
    inst.coreopsarithAddInst.add x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithAddInst.add = U64.Insts.CoreOpsArithAddU64U64.add from rfl,
    U64.Insts.CoreOpsArithAddU64U64.add]
  exact WP.spec_mono (U64.add_spec (by rw [U64.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem sub (x y : U64) (h : InRange 0 18446744073709551615 ((x.val : ℤ) - (y.val : ℤ))) :
    inst.coreopsarithSubInst.sub x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) - (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = U64.Insts.CoreOpsArithSubU64U64.sub from rfl,
    U64.Insts.CoreOpsArithSubU64U64.sub]
  exact WP.spec_mono (U64.sub_spec (x := x) (y := y) (by have := h.1; omega)) fun z hz => by
    have hc := Nat.cast_sub (R := ℤ) hz.2; omega
theorem mul (x y : U64) (h : InRange 0 18446744073709551615 ((x.val : ℤ) * (y.val : ℤ))) :
    inst.coreopsarithMulInst.mul x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) * (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = U64.Insts.CoreOpsArithMulU64U64.mul from rfl,
    U64.Insts.CoreOpsArithMulU64U64.mul]
  exact WP.spec_mono (U64.mul_spec (by rw [U64.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem add_checked (x y : U64) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : U64 => (x.val : ℤ)) 0 18446744073709551615 ((x.val : ℤ) + (y.val : ℤ)) r ⦄ := by
  rw [show inst.add_checked = U64.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := U64.checked_add_bv_spec x y
  rw [U64.max_eq] at h
  cases hr : U64.checked_add x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : U64) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : U64 => (x.val : ℤ)) 0 18446744073709551615 ((x.val : ℤ) - (y.val : ℤ)) r ⦄ := by
  rw [show inst.sub_checked = U64.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := U64.checked_sub_bv_spec x y
  cases hr : U64.checked_sub x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange]
  · omega
  · have hc := Nat.cast_sub (R := ℤ) h.1
    have hx : x.val ≤ 18446744073709551615 := by scalar_tac
    omega
theorem mul_checked (x y : U64) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : U64 => (x.val : ℤ)) 0 18446744073709551615 ((x.val : ℤ) * (y.val : ℤ)) r ⦄ := by
  rw [show inst.mul_checked = U64.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, U64.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := U64.checked_mul_bv_spec x y
  rw [U64.max_eq] at h
  cases hr : U64.checked_mul x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end U64F

theorem faithful_u64 : Faithful U64F.inst (fun x : U64 => (x.val : ℤ)) 0 18446744073709551615 20 :=
  { lo_le := le_refl 0, hi_pos := by norm_num, signed := fun h => absurd h (lt_irrefl 0)
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := U64F.range, inj := U64F.inj
    MIN := U64F.MIN, CHARS := U64F.CHARS, FIRST_SIG := U64F.FIRST_SIG, TAIL := U64F.TAIL
    TREE := U64F.TREE, BITS := U64F.BITS
    from_u8 := U64F.from_u8, from_u16 := U64F.from_u16, from_u32 := U64F.from_u32
    from_u64 := U64F.from_u64, from_u128 := U64F.from_u128, gt := U64F.gt, eq := U64F.eq
    add := U64F.add, sub := U64F.sub, mul := U64F.mul
    add_checked := U64F.add_checked, sub_checked := U64F.sub_checked, mul_checked := U64F.mul_checked }

/-- `parse::<u64>` meets core's `str::parse::<u64>`. -/
theorem parse_spec_u64 : ParseSpec U64F.inst (fun x : U64 => (x.val : ℤ)) 0 18446744073709551615 :=
  parse_spec faithful_u64

/-! ### `u128` -/

namespace U128F

abbrev inst := U128.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : U128) : InRange 0 340282366920938463463374607431768211455 (x.val : ℤ) := ⟨by omega, by scalar_tac⟩
theorem inj (x y : U128) (h : (x.val : ℤ) = (y.val : ℤ)) : x = y := UScalar.eq_of_val_eq (by omega)
theorem MIN : inst.MIN ⦃ m => (m.val : ℤ) = 0 ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 39 ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (340282366920938463463374607431768211455 + 1) / 10 ^ (39 - 1) ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (0 : ℤ) < 0 → (t.val : ℤ) = 0 + ((340282366920938463463374607431768211455 + 1) / 10 ^ (39 - 1)) * 10 ^ (39 - 1) ⦄ := by
  simp [WP.spec_ok]
theorem TREE :
    inst.TREE ⦃ (tr : Slice U128) =>
      tr.val.length = 39 ∧ ∀ i (h : i < tr.val.length), ((tr.val[i]).val : ℤ) = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [U128.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U128, Array.to_slice]
  · intro i h
    simp [U128.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_U128, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 340282366920938463463374607431768211455 - 0 + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.U128.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 340282366920938463463374607431768211455 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u8, UScalar.cast_val_eq]; omega
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 340282366920938463463374607431768211455 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u16, UScalar.cast_val_eq]; omega
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 340282366920938463463374607431768211455 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u32, UScalar.cast_val_eq]; omega
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 340282366920938463463374607431768211455 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u64, UScalar.cast_val_eq]; omega
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 340282366920938463463374607431768211455 → (t.val : ℤ) = u.val ⦄ := by
  simp [WP.spec_ok, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.from_u128]
theorem gt (x y : U128) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide ((y.val : ℤ) < (x.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdU128.gt, liftFun2]
theorem eq (x y : U128) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide ((x.val : ℤ) = (y.val : ℤ)) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqU128.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact UScalar.eq_of_val_eq (by omega)
theorem add (x y : U128) (h : InRange 0 340282366920938463463374607431768211455 ((x.val : ℤ) + (y.val : ℤ))) :
    inst.coreopsarithAddInst.add x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithAddInst.add = U128.Insts.CoreOpsArithAddU128U128.add from rfl,
    U128.Insts.CoreOpsArithAddU128U128.add]
  exact WP.spec_mono (U128.add_spec (by rw [U128.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem sub (x y : U128) (h : InRange 0 340282366920938463463374607431768211455 ((x.val : ℤ) - (y.val : ℤ))) :
    inst.coreopsarithSubInst.sub x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) - (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = U128.Insts.CoreOpsArithSubU128U128.sub from rfl,
    U128.Insts.CoreOpsArithSubU128U128.sub]
  exact WP.spec_mono (U128.sub_spec (x := x) (y := y) (by have := h.1; omega)) fun z hz => by
    have hc := Nat.cast_sub (R := ℤ) hz.2; omega
theorem mul (x y : U128) (h : InRange 0 340282366920938463463374607431768211455 ((x.val : ℤ) * (y.val : ℤ))) :
    inst.coreopsarithMulInst.mul x y ⦃ z => (z.val : ℤ) = (x.val : ℤ) * (y.val : ℤ) ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = U128.Insts.CoreOpsArithMulU128U128.mul from rfl,
    U128.Insts.CoreOpsArithMulU128U128.mul]
  exact WP.spec_mono (U128.mul_spec (by rw [U128.max_eq]; have := h.2; omega)) fun z hz => by exact_mod_cast hz
theorem add_checked (x y : U128) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : U128 => (x.val : ℤ)) 0 340282366920938463463374607431768211455 ((x.val : ℤ) + (y.val : ℤ)) r ⦄ := by
  rw [show inst.add_checked = U128.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := U128.checked_add_bv_spec x y
  rw [U128.max_eq] at h
  cases hr : U128.checked_add x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : U128) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : U128 => (x.val : ℤ)) 0 340282366920938463463374607431768211455 ((x.val : ℤ) - (y.val : ℤ)) r ⦄ := by
  rw [show inst.sub_checked = U128.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := U128.checked_sub_bv_spec x y
  cases hr : U128.checked_sub x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange]
  · omega
  · have hc := Nat.cast_sub (R := ℤ) h.1
    have hx : x.val ≤ 340282366920938463463374607431768211455 := by scalar_tac
    omega
theorem mul_checked (x y : U128) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : U128 => (x.val : ℤ)) 0 340282366920938463463374607431768211455 ((x.val : ℤ) * (y.val : ℤ)) r ⦄ := by
  rw [show inst.mul_checked = U128.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, U128.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := U128.checked_mul_bv_spec x y
  rw [U128.max_eq] at h
  cases hr : U128.checked_mul x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end U128F

theorem faithful_u128 : Faithful U128F.inst (fun x : U128 => (x.val : ℤ)) 0 340282366920938463463374607431768211455 39 :=
  { lo_le := le_refl 0, hi_pos := by norm_num, signed := fun h => absurd h (lt_irrefl 0)
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := U128F.range, inj := U128F.inj
    MIN := U128F.MIN, CHARS := U128F.CHARS, FIRST_SIG := U128F.FIRST_SIG, TAIL := U128F.TAIL
    TREE := U128F.TREE, BITS := U128F.BITS
    from_u8 := U128F.from_u8, from_u16 := U128F.from_u16, from_u32 := U128F.from_u32
    from_u64 := U128F.from_u64, from_u128 := U128F.from_u128, gt := U128F.gt, eq := U128F.eq
    add := U128F.add, sub := U128F.sub, mul := U128F.mul
    add_checked := U128F.add_checked, sub_checked := U128F.sub_checked, mul_checked := U128F.mul_checked }

/-- `parse::<u128>` meets core's `str::parse::<u128>`. -/
theorem parse_spec_u128 : ParseSpec U128F.inst (fun x : U128 => (x.val : ℤ)) 0 340282366920938463463374607431768211455 :=
  parse_spec faithful_u128

/-! ### `i8` -/

namespace I8F

abbrev inst := I8.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : I8) : InRange (-128) 127 x.val := ⟨by scalar_tac, by scalar_tac⟩
theorem inj (x y : I8) (h : x.val = y.val) : x = y := IScalar.eq_of_val_eq h
theorem MIN : inst.MIN ⦃ m => m.val = (-128 : ℤ) ⦄ := by
  simp [WP.spec_ok, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN, I8.rMin]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 3 ⦄ := by
  simp [WP.spec_ok, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (127 + 1) / 10 ^ (3 - 1) ⦄ := by
  simp [WP.spec_ok, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (-128 : ℤ) < 0 → t.val = -128 + ((127 + 1) / 10 ^ (3 - 1)) * 10 ^ (3 - 1) ⦄ := by
  simp [WP.spec_ok, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.TAIL]
theorem TREE :
    inst.TREE ⦃ (tr : Slice I8) =>
      tr.val.length = 3 ∧ ∀ i (h : i < tr.val.length), (tr.val[i]).val = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [I8.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I8, Array.to_slice]
  · intro i h
    simp [I8.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I8, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 127 - (-128) + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.I8.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 127 → t.val = u.val ⦄ := by
  rw [show inst.from_u8 u = ok (UScalar.hcast .I8 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 127 → t.val = u.val ⦄ := by
  rw [show inst.from_u16 u = ok (UScalar.hcast .I8 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 127 → t.val = u.val ⦄ := by
  rw [show inst.from_u32 u = ok (UScalar.hcast .I8 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 127 → t.val = u.val ⦄ := by
  rw [show inst.from_u64 u = ok (UScalar.hcast .I8 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 127 → t.val = u.val ⦄ := by
  rw [show inst.from_u128 u = ok (UScalar.hcast .I8 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem gt (x y : I8) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (y.val < x.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdI8.gt, liftFun2]
theorem eq (x y : I8) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqI8.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h
theorem add (x y : I8) (h : InRange (-128) 127 (x.val + y.val)) :
    inst.coreopsarithAddInst.add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  rw [show inst.coreopsarithAddInst.add = I8.Insts.CoreOpsArithAddI8I8.add from rfl,
    I8.Insts.CoreOpsArithAddI8I8.add]
  exact I8.add_spec (by rw [I8.min_eq]; exact h.1) (by rw [I8.max_eq]; exact h.2)
theorem sub (x y : I8) (h : InRange (-128) 127 (x.val - y.val)) :
    inst.coreopsarithSubInst.sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = I8.Insts.CoreOpsArithSubI8I8.sub from rfl,
    I8.Insts.CoreOpsArithSubI8I8.sub]
  exact I8.sub_spec (by rw [I8.min_eq]; exact h.1) (by rw [I8.max_eq]; exact h.2)
theorem mul (x y : I8) (h : InRange (-128) 127 (x.val * y.val)) :
    inst.coreopsarithMulInst.mul x y ⦃ z => z.val = x.val * y.val ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = I8.Insts.CoreOpsArithMulI8I8.mul from rfl,
    I8.Insts.CoreOpsArithMulI8I8.mul]
  exact I8.mul_spec (by rw [I8.min_eq]; exact h.1) (by rw [I8.max_eq]; exact h.2)
theorem add_checked (x y : I8) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : I8 => x.val) (-128) 127 (x.val + y.val) r ⦄ := by
  rw [show inst.add_checked = I8.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := I8.checked_add_bv_spec x y
  rw [I8.min_eq, I8.max_eq] at h
  rw [show I8.checked_add x y = core.num.checked_add_IScalar x y from rfl]
  cases hr : core.num.checked_add_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : I8) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : I8 => x.val) (-128) 127 (x.val - y.val) r ⦄ := by
  rw [show inst.sub_checked = I8.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := I8.checked_sub_bv_spec x y
  rw [I8.min_eq, I8.max_eq] at h
  rw [show I8.checked_sub x y = core.num.checked_sub_IScalar x y from rfl]
  cases hr : core.num.checked_sub_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem mul_checked (x y : I8) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : I8 => x.val) (-128) 127 (x.val * y.val) r ⦄ := by
  rw [show inst.mul_checked = I8.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, I8.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := I8.checked_mul_bv_spec x y
  rw [I8.min_eq, I8.max_eq] at h
  rw [show I8.checked_mul x y = core.num.checked_mul_IScalar x y from rfl]
  cases hr : core.num.checked_mul_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end I8F

theorem faithful_i8 : Faithful I8F.inst (fun x : I8 => x.val) (-128) 127 3 :=
  { lo_le := by norm_num, hi_pos := by norm_num, signed := fun _ => by norm_num
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := I8F.range, inj := I8F.inj
    MIN := I8F.MIN, CHARS := I8F.CHARS, FIRST_SIG := I8F.FIRST_SIG, TAIL := I8F.TAIL
    TREE := I8F.TREE, BITS := I8F.BITS
    from_u8 := I8F.from_u8, from_u16 := I8F.from_u16, from_u32 := I8F.from_u32
    from_u64 := I8F.from_u64, from_u128 := I8F.from_u128, gt := I8F.gt, eq := I8F.eq
    add := I8F.add, sub := I8F.sub, mul := I8F.mul
    add_checked := I8F.add_checked, sub_checked := I8F.sub_checked, mul_checked := I8F.mul_checked }

/-- `parse::<i8>` meets core's `str::parse::<i8>`. -/
theorem parse_spec_i8 : ParseSpec I8F.inst (fun x : I8 => x.val) (-128) 127 :=
  parse_spec faithful_i8

/-! ### `i16` -/

namespace I16F

abbrev inst := I16.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : I16) : InRange (-32768) 32767 x.val := ⟨by scalar_tac, by scalar_tac⟩
theorem inj (x y : I16) (h : x.val = y.val) : x = y := IScalar.eq_of_val_eq h
theorem MIN : inst.MIN ⦃ m => m.val = (-32768 : ℤ) ⦄ := by
  simp [WP.spec_ok, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN, I16.rMin]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 5 ⦄ := by
  simp [WP.spec_ok, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (32767 + 1) / 10 ^ (5 - 1) ⦄ := by
  simp [WP.spec_ok, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (-32768 : ℤ) < 0 → t.val = -32768 + ((32767 + 1) / 10 ^ (5 - 1)) * 10 ^ (5 - 1) ⦄ := by
  simp [WP.spec_ok, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.TAIL]
theorem TREE :
    inst.TREE ⦃ (tr : Slice I16) =>
      tr.val.length = 5 ∧ ∀ i (h : i < tr.val.length), (tr.val[i]).val = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [I16.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I16, Array.to_slice]
  · intro i h
    simp [I16.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I16, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 32767 - (-32768) + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.I16.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 32767 → t.val = u.val ⦄ := by
  rw [show inst.from_u8 u = ok (UScalar.hcast .I16 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 32767 → t.val = u.val ⦄ := by
  rw [show inst.from_u16 u = ok (UScalar.hcast .I16 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 32767 → t.val = u.val ⦄ := by
  rw [show inst.from_u32 u = ok (UScalar.hcast .I16 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 32767 → t.val = u.val ⦄ := by
  rw [show inst.from_u64 u = ok (UScalar.hcast .I16 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 32767 → t.val = u.val ⦄ := by
  rw [show inst.from_u128 u = ok (UScalar.hcast .I16 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem gt (x y : I16) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (y.val < x.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdI16.gt, liftFun2]
theorem eq (x y : I16) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqI16.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h
theorem add (x y : I16) (h : InRange (-32768) 32767 (x.val + y.val)) :
    inst.coreopsarithAddInst.add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  rw [show inst.coreopsarithAddInst.add = I16.Insts.CoreOpsArithAddI16I16.add from rfl,
    I16.Insts.CoreOpsArithAddI16I16.add]
  exact I16.add_spec (by rw [I16.min_eq]; exact h.1) (by rw [I16.max_eq]; exact h.2)
theorem sub (x y : I16) (h : InRange (-32768) 32767 (x.val - y.val)) :
    inst.coreopsarithSubInst.sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = I16.Insts.CoreOpsArithSubI16I16.sub from rfl,
    I16.Insts.CoreOpsArithSubI16I16.sub]
  exact I16.sub_spec (by rw [I16.min_eq]; exact h.1) (by rw [I16.max_eq]; exact h.2)
theorem mul (x y : I16) (h : InRange (-32768) 32767 (x.val * y.val)) :
    inst.coreopsarithMulInst.mul x y ⦃ z => z.val = x.val * y.val ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = I16.Insts.CoreOpsArithMulI16I16.mul from rfl,
    I16.Insts.CoreOpsArithMulI16I16.mul]
  exact I16.mul_spec (by rw [I16.min_eq]; exact h.1) (by rw [I16.max_eq]; exact h.2)
theorem add_checked (x y : I16) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : I16 => x.val) (-32768) 32767 (x.val + y.val) r ⦄ := by
  rw [show inst.add_checked = I16.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := I16.checked_add_bv_spec x y
  rw [I16.min_eq, I16.max_eq] at h
  rw [show I16.checked_add x y = core.num.checked_add_IScalar x y from rfl]
  cases hr : core.num.checked_add_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : I16) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : I16 => x.val) (-32768) 32767 (x.val - y.val) r ⦄ := by
  rw [show inst.sub_checked = I16.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := I16.checked_sub_bv_spec x y
  rw [I16.min_eq, I16.max_eq] at h
  rw [show I16.checked_sub x y = core.num.checked_sub_IScalar x y from rfl]
  cases hr : core.num.checked_sub_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem mul_checked (x y : I16) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : I16 => x.val) (-32768) 32767 (x.val * y.val) r ⦄ := by
  rw [show inst.mul_checked = I16.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, I16.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := I16.checked_mul_bv_spec x y
  rw [I16.min_eq, I16.max_eq] at h
  rw [show I16.checked_mul x y = core.num.checked_mul_IScalar x y from rfl]
  cases hr : core.num.checked_mul_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end I16F

theorem faithful_i16 : Faithful I16F.inst (fun x : I16 => x.val) (-32768) 32767 5 :=
  { lo_le := by norm_num, hi_pos := by norm_num, signed := fun _ => by norm_num
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := I16F.range, inj := I16F.inj
    MIN := I16F.MIN, CHARS := I16F.CHARS, FIRST_SIG := I16F.FIRST_SIG, TAIL := I16F.TAIL
    TREE := I16F.TREE, BITS := I16F.BITS
    from_u8 := I16F.from_u8, from_u16 := I16F.from_u16, from_u32 := I16F.from_u32
    from_u64 := I16F.from_u64, from_u128 := I16F.from_u128, gt := I16F.gt, eq := I16F.eq
    add := I16F.add, sub := I16F.sub, mul := I16F.mul
    add_checked := I16F.add_checked, sub_checked := I16F.sub_checked, mul_checked := I16F.mul_checked }

/-- `parse::<i16>` meets core's `str::parse::<i16>`. -/
theorem parse_spec_i16 : ParseSpec I16F.inst (fun x : I16 => x.val) (-32768) 32767 :=
  parse_spec faithful_i16

/-! ### `i32` -/

namespace I32F

abbrev inst := I32.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : I32) : InRange (-2147483648) 2147483647 x.val := ⟨by scalar_tac, by scalar_tac⟩
theorem inj (x y : I32) (h : x.val = y.val) : x = y := IScalar.eq_of_val_eq h
theorem MIN : inst.MIN ⦃ m => m.val = (-2147483648 : ℤ) ⦄ := by
  simp [WP.spec_ok, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN, I32.rMin]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 10 ⦄ := by
  simp [WP.spec_ok, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (2147483647 + 1) / 10 ^ (10 - 1) ⦄ := by
  simp [WP.spec_ok, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (-2147483648 : ℤ) < 0 → t.val = -2147483648 + ((2147483647 + 1) / 10 ^ (10 - 1)) * 10 ^ (10 - 1) ⦄ := by
  simp [WP.spec_ok, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.TAIL]
theorem TREE :
    inst.TREE ⦃ (tr : Slice I32) =>
      tr.val.length = 10 ∧ ∀ i (h : i < tr.val.length), (tr.val[i]).val = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [I32.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I32, Array.to_slice]
  · intro i h
    simp [I32.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I32, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 2147483647 - (-2147483648) + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.I32.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 2147483647 → t.val = u.val ⦄ := by
  rw [show inst.from_u8 u = ok (UScalar.hcast .I32 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 2147483647 → t.val = u.val ⦄ := by
  rw [show inst.from_u16 u = ok (UScalar.hcast .I32 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 2147483647 → t.val = u.val ⦄ := by
  rw [show inst.from_u32 u = ok (UScalar.hcast .I32 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 2147483647 → t.val = u.val ⦄ := by
  rw [show inst.from_u64 u = ok (UScalar.hcast .I32 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 2147483647 → t.val = u.val ⦄ := by
  rw [show inst.from_u128 u = ok (UScalar.hcast .I32 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem gt (x y : I32) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (y.val < x.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdI32.gt, liftFun2]
theorem eq (x y : I32) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqI32.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h
theorem add (x y : I32) (h : InRange (-2147483648) 2147483647 (x.val + y.val)) :
    inst.coreopsarithAddInst.add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  rw [show inst.coreopsarithAddInst.add = I32.Insts.CoreOpsArithAddI32I32.add from rfl,
    I32.Insts.CoreOpsArithAddI32I32.add]
  exact I32.add_spec (by rw [I32.min_eq]; exact h.1) (by rw [I32.max_eq]; exact h.2)
theorem sub (x y : I32) (h : InRange (-2147483648) 2147483647 (x.val - y.val)) :
    inst.coreopsarithSubInst.sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = I32.Insts.CoreOpsArithSubI32I32.sub from rfl,
    I32.Insts.CoreOpsArithSubI32I32.sub]
  exact I32.sub_spec (by rw [I32.min_eq]; exact h.1) (by rw [I32.max_eq]; exact h.2)
theorem mul (x y : I32) (h : InRange (-2147483648) 2147483647 (x.val * y.val)) :
    inst.coreopsarithMulInst.mul x y ⦃ z => z.val = x.val * y.val ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = I32.Insts.CoreOpsArithMulI32I32.mul from rfl,
    I32.Insts.CoreOpsArithMulI32I32.mul]
  exact I32.mul_spec (by rw [I32.min_eq]; exact h.1) (by rw [I32.max_eq]; exact h.2)
theorem add_checked (x y : I32) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : I32 => x.val) (-2147483648) 2147483647 (x.val + y.val) r ⦄ := by
  rw [show inst.add_checked = I32.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := I32.checked_add_bv_spec x y
  rw [I32.min_eq, I32.max_eq] at h
  rw [show I32.checked_add x y = core.num.checked_add_IScalar x y from rfl]
  cases hr : core.num.checked_add_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : I32) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : I32 => x.val) (-2147483648) 2147483647 (x.val - y.val) r ⦄ := by
  rw [show inst.sub_checked = I32.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := I32.checked_sub_bv_spec x y
  rw [I32.min_eq, I32.max_eq] at h
  rw [show I32.checked_sub x y = core.num.checked_sub_IScalar x y from rfl]
  cases hr : core.num.checked_sub_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem mul_checked (x y : I32) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : I32 => x.val) (-2147483648) 2147483647 (x.val * y.val) r ⦄ := by
  rw [show inst.mul_checked = I32.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, I32.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := I32.checked_mul_bv_spec x y
  rw [I32.min_eq, I32.max_eq] at h
  rw [show I32.checked_mul x y = core.num.checked_mul_IScalar x y from rfl]
  cases hr : core.num.checked_mul_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end I32F

theorem faithful_i32 : Faithful I32F.inst (fun x : I32 => x.val) (-2147483648) 2147483647 10 :=
  { lo_le := by norm_num, hi_pos := by norm_num, signed := fun _ => by norm_num
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := I32F.range, inj := I32F.inj
    MIN := I32F.MIN, CHARS := I32F.CHARS, FIRST_SIG := I32F.FIRST_SIG, TAIL := I32F.TAIL
    TREE := I32F.TREE, BITS := I32F.BITS
    from_u8 := I32F.from_u8, from_u16 := I32F.from_u16, from_u32 := I32F.from_u32
    from_u64 := I32F.from_u64, from_u128 := I32F.from_u128, gt := I32F.gt, eq := I32F.eq
    add := I32F.add, sub := I32F.sub, mul := I32F.mul
    add_checked := I32F.add_checked, sub_checked := I32F.sub_checked, mul_checked := I32F.mul_checked }

/-- `parse::<i32>` meets core's `str::parse::<i32>`. -/
theorem parse_spec_i32 : ParseSpec I32F.inst (fun x : I32 => x.val) (-2147483648) 2147483647 :=
  parse_spec faithful_i32

/-! ### `i64` -/

namespace I64F

abbrev inst := I64.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : I64) : InRange (-9223372036854775808) 9223372036854775807 x.val := ⟨by scalar_tac, by scalar_tac⟩
theorem inj (x y : I64) (h : x.val = y.val) : x = y := IScalar.eq_of_val_eq h
theorem MIN : inst.MIN ⦃ m => m.val = (-9223372036854775808 : ℤ) ⦄ := by
  simp [WP.spec_ok, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN, I64.rMin]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 19 ⦄ := by
  simp [WP.spec_ok, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (9223372036854775807 + 1) / 10 ^ (19 - 1) ⦄ := by
  simp [WP.spec_ok, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (-9223372036854775808 : ℤ) < 0 → t.val = -9223372036854775808 + ((9223372036854775807 + 1) / 10 ^ (19 - 1)) * 10 ^ (19 - 1) ⦄ := by
  simp [WP.spec_ok, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.TAIL]
theorem TREE :
    inst.TREE ⦃ (tr : Slice I64) =>
      tr.val.length = 19 ∧ ∀ i (h : i < tr.val.length), (tr.val[i]).val = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [I64.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I64, Array.to_slice]
  · intro i h
    simp [I64.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I64, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 9223372036854775807 - (-9223372036854775808) + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.I64.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 9223372036854775807 → t.val = u.val ⦄ := by
  rw [show inst.from_u8 u = ok (UScalar.hcast .I64 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 9223372036854775807 → t.val = u.val ⦄ := by
  rw [show inst.from_u16 u = ok (UScalar.hcast .I64 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 9223372036854775807 → t.val = u.val ⦄ := by
  rw [show inst.from_u32 u = ok (UScalar.hcast .I64 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 9223372036854775807 → t.val = u.val ⦄ := by
  rw [show inst.from_u64 u = ok (UScalar.hcast .I64 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 9223372036854775807 → t.val = u.val ⦄ := by
  rw [show inst.from_u128 u = ok (UScalar.hcast .I64 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem gt (x y : I64) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (y.val < x.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdI64.gt, liftFun2]
theorem eq (x y : I64) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqI64.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h
theorem add (x y : I64) (h : InRange (-9223372036854775808) 9223372036854775807 (x.val + y.val)) :
    inst.coreopsarithAddInst.add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  rw [show inst.coreopsarithAddInst.add = I64.Insts.CoreOpsArithAddI64I64.add from rfl,
    I64.Insts.CoreOpsArithAddI64I64.add]
  exact I64.add_spec (by rw [I64.min_eq]; exact h.1) (by rw [I64.max_eq]; exact h.2)
theorem sub (x y : I64) (h : InRange (-9223372036854775808) 9223372036854775807 (x.val - y.val)) :
    inst.coreopsarithSubInst.sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = I64.Insts.CoreOpsArithSubI64I64.sub from rfl,
    I64.Insts.CoreOpsArithSubI64I64.sub]
  exact I64.sub_spec (by rw [I64.min_eq]; exact h.1) (by rw [I64.max_eq]; exact h.2)
theorem mul (x y : I64) (h : InRange (-9223372036854775808) 9223372036854775807 (x.val * y.val)) :
    inst.coreopsarithMulInst.mul x y ⦃ z => z.val = x.val * y.val ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = I64.Insts.CoreOpsArithMulI64I64.mul from rfl,
    I64.Insts.CoreOpsArithMulI64I64.mul]
  exact I64.mul_spec (by rw [I64.min_eq]; exact h.1) (by rw [I64.max_eq]; exact h.2)
theorem add_checked (x y : I64) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : I64 => x.val) (-9223372036854775808) 9223372036854775807 (x.val + y.val) r ⦄ := by
  rw [show inst.add_checked = I64.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := I64.checked_add_bv_spec x y
  rw [I64.min_eq, I64.max_eq] at h
  rw [show I64.checked_add x y = core.num.checked_add_IScalar x y from rfl]
  cases hr : core.num.checked_add_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : I64) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : I64 => x.val) (-9223372036854775808) 9223372036854775807 (x.val - y.val) r ⦄ := by
  rw [show inst.sub_checked = I64.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := I64.checked_sub_bv_spec x y
  rw [I64.min_eq, I64.max_eq] at h
  rw [show I64.checked_sub x y = core.num.checked_sub_IScalar x y from rfl]
  cases hr : core.num.checked_sub_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem mul_checked (x y : I64) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : I64 => x.val) (-9223372036854775808) 9223372036854775807 (x.val * y.val) r ⦄ := by
  rw [show inst.mul_checked = I64.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, I64.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := I64.checked_mul_bv_spec x y
  rw [I64.min_eq, I64.max_eq] at h
  rw [show I64.checked_mul x y = core.num.checked_mul_IScalar x y from rfl]
  cases hr : core.num.checked_mul_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end I64F

theorem faithful_i64 : Faithful I64F.inst (fun x : I64 => x.val) (-9223372036854775808) 9223372036854775807 19 :=
  { lo_le := by norm_num, hi_pos := by norm_num, signed := fun _ => by norm_num
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := I64F.range, inj := I64F.inj
    MIN := I64F.MIN, CHARS := I64F.CHARS, FIRST_SIG := I64F.FIRST_SIG, TAIL := I64F.TAIL
    TREE := I64F.TREE, BITS := I64F.BITS
    from_u8 := I64F.from_u8, from_u16 := I64F.from_u16, from_u32 := I64F.from_u32
    from_u64 := I64F.from_u64, from_u128 := I64F.from_u128, gt := I64F.gt, eq := I64F.eq
    add := I64F.add, sub := I64F.sub, mul := I64F.mul
    add_checked := I64F.add_checked, sub_checked := I64F.sub_checked, mul_checked := I64F.mul_checked }

/-- `parse::<i64>` meets core's `str::parse::<i64>`. -/
theorem parse_spec_i64 : ParseSpec I64F.inst (fun x : I64 => x.val) (-9223372036854775808) 9223372036854775807 :=
  parse_spec faithful_i64

/-! ### `i128` -/

namespace I128F

abbrev inst := I128.Insts.Atoi_radix10ParseFromStrRadixHelper

theorem range (x : I128) : InRange (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 x.val := ⟨by scalar_tac, by scalar_tac⟩
theorem inj (x y : I128) (h : x.val = y.val) : x = y := IScalar.eq_of_val_eq h
theorem MIN : inst.MIN ⦃ m => m.val = (-170141183460469231731687303715884105728 : ℤ) ⦄ := by
  simp [WP.spec_ok, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.MIN, I128.rMin]
theorem CHARS : inst.CHARS ⦃ (n : Usize) => n.val = 39 ⦄ := by
  simp [WP.spec_ok, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.CHARS]
theorem FIRST_SIG : inst.FIRST_SIG ⦃ (f : U8) => (f.val : ℤ) = (170141183460469231731687303715884105727 + 1) / 10 ^ (39 - 1) ⦄ := by
  simp [WP.spec_ok, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.FIRST_SIG]
theorem TAIL :
    inst.TAIL ⦃ t => (-170141183460469231731687303715884105728 : ℤ) < 0 → t.val = -170141183460469231731687303715884105728 + ((170141183460469231731687303715884105727 + 1) / 10 ^ (39 - 1)) * 10 ^ (39 - 1) ⦄ := by
  simp [WP.spec_ok, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.TAIL]
theorem TREE :
    inst.TREE ⦃ (tr : Slice I128) =>
      tr.val.length = 39 ∧ ∀ i (h : i < tr.val.length), (tr.val[i]).val = 10 ^ i ⦄ := by
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · simp [I128.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I128, Array.to_slice]
  · intro i h
    simp [I128.Insts.Atoi_radix10ParseFromStrRadixHelper.TREE, trees.TENS_I128, Array.to_slice] at h ⊢
    interval_cases i <;> simp
theorem BITS : inst.BITS ⦃ (b : U32) => (2 : ℤ) ^ b.val = 170141183460469231731687303715884105727 - (-170141183460469231731687303715884105728) + 1 ∧
    (b.val = 8 ∨ b.val = 16 ∨ b.val = 32 ∨ b.val = 64 ∨ b.val = 128) ⦄ := by
  simp [WP.spec_ok, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.BITS, core.num.I128.BITS]
theorem from_u8 (u : U8) : inst.from_u8 u ⦃ t => (u.val : ℤ) ≤ 170141183460469231731687303715884105727 → t.val = u.val ⦄ := by
  rw [show inst.from_u8 u = ok (UScalar.hcast .I128 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u16 (u : U16) : inst.from_u16 u ⦃ t => (u.val : ℤ) ≤ 170141183460469231731687303715884105727 → t.val = u.val ⦄ := by
  rw [show inst.from_u16 u = ok (UScalar.hcast .I128 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u32 (u : U32) : inst.from_u32 u ⦃ t => (u.val : ℤ) ≤ 170141183460469231731687303715884105727 → t.val = u.val ⦄ := by
  rw [show inst.from_u32 u = ok (UScalar.hcast .I128 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u64 (u : U64) : inst.from_u64 u ⦃ t => (u.val : ℤ) ≤ 170141183460469231731687303715884105727 → t.val = u.val ⦄ := by
  rw [show inst.from_u64 u = ok (UScalar.hcast .I128 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem from_u128 (u : U128) : inst.from_u128 u ⦃ t => (u.val : ℤ) ≤ 170141183460469231731687303715884105727 → t.val = u.val ⦄ := by
  rw [show inst.from_u128 u = ok (UScalar.hcast .I128 u) from rfl, WP.spec_ok]
  intro hu
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by norm_num [IScalarTy.numBits]) (by norm_num [IScalarTy.numBits]; omega)
theorem gt (x y : I128) :
    inst.corecmpPartialOrdInst.gt x y ⦃ b => b = decide (y.val < x.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialOrdI128.gt, liftFun2]
theorem eq (x y : I128) :
    inst.corecmpPartialOrdInst.partialEqInst.eq x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  simp [WP.spec_ok, core.cmp.impls.PartialEqI128.eq, liftFun2]
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h
theorem add (x y : I128) (h : InRange (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val + y.val)) :
    inst.coreopsarithAddInst.add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  rw [show inst.coreopsarithAddInst.add = I128.Insts.CoreOpsArithAddI128I128.add from rfl,
    I128.Insts.CoreOpsArithAddI128I128.add]
  exact I128.add_spec (by rw [I128.min_eq]; exact h.1) (by rw [I128.max_eq]; exact h.2)
theorem sub (x y : I128) (h : InRange (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val - y.val)) :
    inst.coreopsarithSubInst.sub x y ⦃ z => z.val = x.val - y.val ⦄ := by
  rw [show inst.coreopsarithSubInst.sub = I128.Insts.CoreOpsArithSubI128I128.sub from rfl,
    I128.Insts.CoreOpsArithSubI128I128.sub]
  exact I128.sub_spec (by rw [I128.min_eq]; exact h.1) (by rw [I128.max_eq]; exact h.2)
theorem mul (x y : I128) (h : InRange (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val * y.val)) :
    inst.coreopsarithMulInst.mul x y ⦃ z => z.val = x.val * y.val ⦄ := by
  rw [show inst.coreopsarithMulInst.mul = I128.Insts.CoreOpsArithMulI128I128.mul from rfl,
    I128.Insts.CoreOpsArithMulI128I128.mul]
  exact I128.mul_spec (by rw [I128.min_eq]; exact h.1) (by rw [I128.max_eq]; exact h.2)
theorem add_checked (x y : I128) :
    inst.add_checked x y ⦃ r => CheckedIs (fun x : I128 => x.val) (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val + y.val) r ⦄ := by
  rw [show inst.add_checked = I128.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked from rfl, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.add_checked, WP.spec_ok]
  have h := I128.checked_add_bv_spec x y
  rw [I128.min_eq, I128.max_eq] at h
  rw [show I128.checked_add x y = core.num.checked_add_IScalar x y from rfl]
  cases hr : core.num.checked_add_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem sub_checked (x y : I128) :
    inst.sub_checked x y ⦃ r => CheckedIs (fun x : I128 => x.val) (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val - y.val) r ⦄ := by
  rw [show inst.sub_checked = I128.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked from rfl, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.sub_checked, WP.spec_ok]
  have h := I128.checked_sub_bv_spec x y
  rw [I128.min_eq, I128.max_eq] at h
  rw [show I128.checked_sub x y = core.num.checked_sub_IScalar x y from rfl]
  cases hr : core.num.checked_sub_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega
theorem mul_checked (x y : I128) :
    inst.mul_checked x y ⦃ r => CheckedIs (fun x : I128 => x.val) (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 (x.val * y.val) r ⦄ := by
  rw [show inst.mul_checked = I128.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked from rfl, I128.Insts.Atoi_radix10ParseFromStrRadixHelper.mul_checked, WP.spec_ok]
  have h := I128.checked_mul_bv_spec x y
  rw [I128.min_eq, I128.max_eq] at h
  rw [show I128.checked_mul x y = core.num.checked_mul_IScalar x y from rfl]
  cases hr : core.num.checked_mul_IScalar x y <;> simp only [hr] at h <;> simp only [CheckedIs, InRange] <;> omega

end I128F

theorem faithful_i128 : Faithful I128F.inst (fun x : I128 => x.val) (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 39 :=
  { lo_le := by norm_num, hi_pos := by norm_num, signed := fun _ => by norm_num
    hi_lt := by norm_num, hi_ge := by norm_num, three_le_c := by norm_num, fs_mul_le := by norm_num
    range := I128F.range, inj := I128F.inj
    MIN := I128F.MIN, CHARS := I128F.CHARS, FIRST_SIG := I128F.FIRST_SIG, TAIL := I128F.TAIL
    TREE := I128F.TREE, BITS := I128F.BITS
    from_u8 := I128F.from_u8, from_u16 := I128F.from_u16, from_u32 := I128F.from_u32
    from_u64 := I128F.from_u64, from_u128 := I128F.from_u128, gt := I128F.gt, eq := I128F.eq
    add := I128F.add, sub := I128F.sub, mul := I128F.mul
    add_checked := I128F.add_checked, sub_checked := I128F.sub_checked, mul_checked := I128F.mul_checked }

/-- `parse::<i128>` meets core's `str::parse::<i128>`. -/
theorem parse_spec_i128 : ParseSpec I128F.inst (fun x : I128 => x.val) (-170141183460469231731687303715884105728) 170141183460469231731687303715884105727 :=
  parse_spec faithful_i128

end atoi_radix10
