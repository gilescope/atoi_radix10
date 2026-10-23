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

The shipped code. The four raw-pointer word loads and the address test behind the SWAR parsers
live in `src/load.rs` as `#[inline(always)]` wrappers (the same instructions as before) and are
left opaque to Charon (`--opaque` in the Earthfile), because Aeneas has no memory model to give
them a meaning. `AtoiRadix10/FunsExternal.lean` models each load as the little-endian value of
the first `N` bytes, failing when the slice is shorter. That model is the trust boundary: it says
an aligned `N`-byte read on a little-endian target yields the little-endian value of the bytes,
and it leaves the memory safety of the reads (length and alignment) to Miri and the fuzzers.

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

## Not yet

The generic `parse<T>` (`src/parse.rs`): Aeneas duplicated the code after each of its 71 `if`s
and ran out of memory. The fork's `-join-early-exits` (branch `giles-join-early-exit`) fixes
that by joining the branches that fall through; `parse` is the next target once the pin moves.
