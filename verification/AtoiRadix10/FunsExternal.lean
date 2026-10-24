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

/-! ### The externals of `parse`

`core`'s own items that Aeneas has no model for, and the alignment test. -/

/-- `load::misaligned`: `s.as_ptr() as usize & bit != 0`, a fact about the address, of which the
model knows nothing. Left uninterpreted: a theorem about `parse` then holds for every answer at
every call, so for the answers the real addresses give. (The calls of one run differ in `bit`
or in the slice, so a function of the two realises any run.) -/
opaque load.misaligned (_s : Slice U8) (_bit : Usize) : Result Bool := ok false

/-- `<[T]>::first`. -/
def core.slice.Slice.first {T : Type} (s : Slice T) : Result (Option T) := ok s.val.head?

/-- `str::as_bytes`: Aeneas's `Str` is already the bytes. -/
def core.str.Str.as_bytes (s : Str) : Result (Slice U8) := ok s

/-- The derived `Debug` and `PartialEq` of `IntErrorKind`; `parse` calls neither. -/
def core.num.error.IntErrorKind.Insts.CoreFmtDebug.fmt (_ : core.num.error.IntErrorKind)
    (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (.Ok (), f)

deriving instance DecidableEq for core.num.error.IntErrorKind

def core.num.error.IntErrorKind.Insts.CoreCmpPartialEqIntErrorKind.eq
    (a b : core.num.error.IntErrorKind) : Result Bool :=
  ok (decide (a = b))

/-- `impl Add/Sub/Mul for <int>`: the operators, with Aeneas's meaning of `+`, `-` and `*` on
machine integers, which fail on overflow. Release Rust wraps instead; a proof that `parse` meets
its specification under the failing meaning therefore also shows no operation ever overflows,
so the wrapping meaning is never reached. -/
def I8.Insts.CoreOpsArithAddI8I8.add (x y : I8) : Result I8 := x + y
def I16.Insts.CoreOpsArithAddI16I16.add (x y : I16) : Result I16 := x + y
def I32.Insts.CoreOpsArithAddI32I32.add (x y : I32) : Result I32 := x + y
def I64.Insts.CoreOpsArithAddI64I64.add (x y : I64) : Result I64 := x + y
def I128.Insts.CoreOpsArithAddI128I128.add (x y : I128) : Result I128 := x + y
def U8.Insts.CoreOpsArithAddU8U8.add (x y : U8) : Result U8 := x + y
def U16.Insts.CoreOpsArithAddU16U16.add (x y : U16) : Result U16 := x + y
def U32.Insts.CoreOpsArithAddU32U32.add (x y : U32) : Result U32 := x + y
def U64.Insts.CoreOpsArithAddU64U64.add (x y : U64) : Result U64 := x + y
def U128.Insts.CoreOpsArithAddU128U128.add (x y : U128) : Result U128 := x + y
def I8.Insts.CoreOpsArithSubI8I8.sub (x y : I8) : Result I8 := x - y
def I16.Insts.CoreOpsArithSubI16I16.sub (x y : I16) : Result I16 := x - y
def I32.Insts.CoreOpsArithSubI32I32.sub (x y : I32) : Result I32 := x - y
def I64.Insts.CoreOpsArithSubI64I64.sub (x y : I64) : Result I64 := x - y
def I128.Insts.CoreOpsArithSubI128I128.sub (x y : I128) : Result I128 := x - y
def U8.Insts.CoreOpsArithSubU8U8.sub (x y : U8) : Result U8 := x - y
def U16.Insts.CoreOpsArithSubU16U16.sub (x y : U16) : Result U16 := x - y
def U32.Insts.CoreOpsArithSubU32U32.sub (x y : U32) : Result U32 := x - y
def U64.Insts.CoreOpsArithSubU64U64.sub (x y : U64) : Result U64 := x - y
def U128.Insts.CoreOpsArithSubU128U128.sub (x y : U128) : Result U128 := x - y
def I8.Insts.CoreOpsArithMulI8I8.mul (x y : I8) : Result I8 := x * y
def I16.Insts.CoreOpsArithMulI16I16.mul (x y : I16) : Result I16 := x * y
def I32.Insts.CoreOpsArithMulI32I32.mul (x y : I32) : Result I32 := x * y
def I64.Insts.CoreOpsArithMulI64I64.mul (x y : I64) : Result I64 := x * y
def I128.Insts.CoreOpsArithMulI128I128.mul (x y : I128) : Result I128 := x * y
def U8.Insts.CoreOpsArithMulU8U8.mul (x y : U8) : Result U8 := x * y
def U16.Insts.CoreOpsArithMulU16U16.mul (x y : U16) : Result U16 := x * y
def U32.Insts.CoreOpsArithMulU32U32.mul (x y : U32) : Result U32 := x * y
def U64.Insts.CoreOpsArithMulU64U64.mul (x y : U64) : Result U64 := x * y
def U128.Insts.CoreOpsArithMulU128U128.mul (x y : U128) : Result U128 := x * y

end atoi_radix10
