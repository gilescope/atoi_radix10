module
public import Aeneas
public import AtoiRadix10.Types
@[expose] public section

/-!
Hand-written models of the functions left opaque to Charon (`--opaque` in the Earthfile): the
word loads behind the SWAR parsers, which read `*(s.as_ptr() as *const uN)` and so have no
meaning inside Aeneas. These are trusted, so each must stay obviously equal to the Rust it
names (`src/load.rs`): an aligned `N`-byte read on a little-endian target is the
little-endian value of the first `N` bytes, and reading past the slice is undefined, which
the model makes a failure. `earthly +extract` regenerates `FunsExternal_Template.lean`:
when a Rust change adds an external, the build fails here until a model is written.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The little-endian value of a list of bytes. -/
def leBytes : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * leBytes bs

/-- The first `n` bytes of `s`, little-endian: what the aligned `n`-byte load yields. -/
def loadLE (n : Nat) (s : Slice U8) : Result Nat :=
  if n ≤ s.val.length then ok (leBytes (s.val.take n)) else fail .undef

/-- `load::load_u16`: `*(s.as_ptr() as *const u16)`. -/
def load.load_u16 (s : Slice U8) : Result U16 := do
  let n ← loadLE 2 s
  ok ⟨BitVec.ofNat 16 n⟩

/-- `load::load_u32`: `*(s.as_ptr() as *const u32)`. -/
def load.load_u32 (s : Slice U8) : Result U32 := do
  let n ← loadLE 4 s
  ok ⟨BitVec.ofNat 32 n⟩

/-- `load::load_u64`: `*(s.as_ptr() as *const u64)`. -/
def load.load_u64 (s : Slice U8) : Result U64 := do
  let n ← loadLE 8 s
  ok ⟨BitVec.ofNat 64 n⟩

/-- `load::load_u128`: `*(s.as_ptr() as *const u128)`. -/
def load.load_u128 (s : Slice U8) : Result U128 := do
  let n ← loadLE 16 s
  ok ⟨BitVec.ofNat 128 n⟩

end atoi_radix10
