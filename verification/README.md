# Aeneas proofs

Lean proofs about the Rust in `src/`, checked against the model
[Aeneas](https://github.com/AeneasVerif/aeneas) extracts from that Rust - not a hand copy.

```sh
earthly +prove     # charon -> aeneas -> lake build: model, proofs, axiom audit
earthly +extract   # also writes the generated model here for editor use (git-ignored)
```

Everything runs in the `+tools` image (pinned in the root `Earthfile`: the
[gilescope/aeneas](https://github.com/gilescope/aeneas) fork, Charon at its pin, Lean 4.34).
For editing proofs on a laptop, `scripts/dev-link.sh <aeneas-checkout>` points `.aeneas` at a
built checkout of the fork's backend and `lake build` works as usual.

## What is extracted

The shipped code, every function of the crate but the `usize`/`isize` instances (Lean keeps the
platform word size abstract, 32 or 64 bits, so their 64-bit tables cannot be shown in range;
their `parse` is the same generic code). The generic `parse<T>` needs the fork's
`-join-early-exits`: without it Aeneas duplicates the code after each of its 71 `if`s and runs
out of memory.

The four raw-pointer word loads and the address test behind the SWAR parsers live in
`src/load.rs` as `#[inline(always)]` wrappers (the same instructions as before) and are left
opaque to Charon (`--opaque` in the Earthfile), because Aeneas has no memory model to give them
a meaning. `AtoiRadix10/FunsExternal.lean` models each load as the little-endian value of the
first `N` bytes, failing when the slice is shorter, and leaves `misaligned` uninterpreted, so
every theorem holds whichever alignment branch runs. That model is the trust boundary: it says
an aligned `N`-byte read on a little-endian target yields the little-endian value of the bytes,
and it leaves the memory safety of the reads (length and alignment) to Miri and the fuzzers.
The same file gives core's `Add`/`Sub`/`Mul` for the integer types Aeneas's meaning, which
fails on overflow: a proof under it also shows no operation overflows.

## Proved (`Proofs/`)

Kernel-checked, resting on Lean's three standard axioms only: no `sorry`, no `native_decide`,
no `bv_decide`. `Audit.lean` fails the build otherwise.

| Rust (`src/lib.rs`) | Spec                                                                        |
| ------------------- | --------------------------------------------------------------------------- |
| `load_u{16,32,64,128}` (model) | value = little-endian fold of the first N bytes, fits the word     |
| `parse_2_chars`     | `Ok(10 d0 + d1)` iff both bytes are ASCII digits, else `Err(InvalidDigit)` |
| `parse_4_chars`     | the same, four digits, value `1000 d0 + … + d3`                             |
| `parse_8_chars`     | the same, eight digits                                                      |
| `parse_16_chars`    | the same, sixteen digits                                                    |
| `parse_32_chars`    | the same, 32 digits: both halves digits, value `10^16 · hi + lo`            |

Each holds for any slice at least that long, whatever its alignment, and says no arithmetic
overflows on the way (every `+`, `*` and `<<` in the extracted model is checked).

How: `Proofs/Lanes.lean` reads a word as lanes of `w` bits (`lanes w xs`), with bitwise
operations, additions, scalings, whole-lane shifts and casts acting lane by lane;
`Proofs/Fold.lean` is one SWAR fold step (`((x & odd) >> w) + (x & even) · c` groups adjacent
digit lanes); `Proofs/DigitTest.lean` is the digit test (`c & 0xf0.. = 0` and
`(c +wrap 0x76..) & 0x80.. = 0` exactly when every byte is a digit), with the per-byte facts
decided over the 256 bytes.

## `parse<T>` (`Proofs/Parse.lean`, `Proofs/Final.lean`)

`Proofs/Ref.lean` is the reference, core's `from_str_radix` over the integers (`stdParse lo hi`),
and `ParseSpec` says `parse` is it: the same `Ok` values, `Err` exactly where core errs, with
the same `IntErrorKind`. `parse` is `parse_inner`, the fast path, which decides `Ok`/`Err` and
the value but reports the first thing that stopped it (`Empty` for a lone sign, an overflow for
a bad byte after an overflowing run), followed on the error path by `std_error_kind`, core's
digit fold with no value kept, which recomputes the kind (`Proofs/Kind.lean`).
`parse_inner_spec` proves the fast path against `stdParse` up to `kindLike` (core's
`InvalidDigit` may come back as any kind), `std_error_kind_spec` proves the classifier returns
core's kind on every input core rejects, and `parse_spec` combines them, for any `Faithful`
instance of `FromStrRadixHelper`, the record of facts about the methods that `doit!`
guarantees; `faithful_u8` .. `faithful_i128` (`Proofs/Parse.lean`, `Proofs/Instances.lean`)
prove those facts for each of the ten integer types, so `parse_spec_u8` .. `parse_spec_i128`
are the theorems for `parse::<T>` at every `T` the crate ships (`usize`/`isize` are excluded
from extraction: their width is platform-abstract in Aeneas).

The seven extracted loops each have their lemma: the sign dispatch
(`Proofs/Sign.lean`), the positive pre-pass and the two leading-zero loops
(`Proofs/ParseLoops.lean`), the positive SWAR block (`Proofs/Block.lean`), the negative pre-pass
and block (`Proofs/NegPre.lean`, `Proofs/NegLoop.lean`); `Proofs/StdDigits.lean` has the fold's
closed forms.
