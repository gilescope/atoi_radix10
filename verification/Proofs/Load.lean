import AtoiRadix10

/-!
Specs for the load models (`AtoiRadix10/FunsExternal.lean`): a load of `n` bytes succeeds
exactly when the slice holds them, and its value is the little-endian value of those bytes,
which fits the word.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

theorem leBytes_lt (bs : List U8) : leBytes bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leBytes]
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [leBytes, List.length_cons, Nat.pow_succ]
    omega

theorem leBytes_append (xs ys : List U8) :
    leBytes (xs ++ ys) = leBytes xs + 256 ^ xs.length * leBytes ys := by
  induction xs with
  | nil => simp [leBytes]
  | cons x xs ih => simp only [List.cons_append, leBytes, ih, List.length_cons, Nat.pow_succ]; ring

theorem loadLE_spec (n : Nat) (s : Slice U8) (h : n ≤ s.val.length) :
    loadLE n s = ok (leBytes (s.val.take n)) := by
  simp [loadLE, h]

theorem leBytes_take_lt (n : Nat) (s : Slice U8) (h : n ≤ s.val.length) :
    leBytes (s.val.take n) < 256 ^ n := by
  have := leBytes_lt (s.val.take n)
  rwa [List.length_take, Nat.min_eq_left h] at this

@[step] theorem load.load_u16_spec (s : Slice U8) (h : 2 ≤ s.val.length) :
    load.load_u16 s ⦃ v => v.val = leBytes (s.val.take 2) ⦄ := by
  have hlt := leBytes_take_lt 2 s h
  simp only [load.load_u16, loadLE_spec 2 s h, bind_ok, WP.spec_ok]
  show (BitVec.ofNat 16 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; omega)]

@[step] theorem load.load_u32_spec (s : Slice U8) (h : 4 ≤ s.val.length) :
    load.load_u32 s ⦃ v => v.val = leBytes (s.val.take 4) ⦄ := by
  have hlt := leBytes_take_lt 4 s h
  simp only [load.load_u32, loadLE_spec 4 s h, bind_ok, WP.spec_ok]
  show (BitVec.ofNat 32 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; omega)]

@[step] theorem load.load_u64_spec (s : Slice U8) (h : 8 ≤ s.val.length) :
    load.load_u64 s ⦃ v => v.val = leBytes (s.val.take 8) ⦄ := by
  have hlt := leBytes_take_lt 8 s h
  simp only [load.load_u64, loadLE_spec 8 s h, bind_ok, WP.spec_ok]
  show (BitVec.ofNat 64 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; omega)]

@[step] theorem load.load_u128_spec (s : Slice U8) (h : 16 ≤ s.val.length) :
    load.load_u128 s ⦃ v => v.val = leBytes (s.val.take 16) ⦄ := by
  have hlt := leBytes_take_lt 16 s h
  simp only [load.load_u128, loadLE_spec 16 s h, bind_ok, WP.spec_ok]
  show (BitVec.ofNat 128 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; omega)]

end atoi_radix10
