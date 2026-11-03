import Lake
open Lake DSL

/-- The Aeneas fork's Lean backend: `.aeneas` is a symlink. In `+prove` it points into the Lake
cache mount, at a copy of the `+tools` image's sources (pinned by `AENEAS_COMMIT` in the
Earthfile) that `lake build` compiles there; locally, at a checkout of the fork
(`scripts/dev-link.sh`). A relative path so the manifest is the same everywhere. -/
require aeneas from ".aeneas"

/-- Aeneas's Mathlib, required explicitly so its pin wins for the shared dependencies. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

/-- Warnings are errors in our own modules only: `lake build --wfail` would also fail on the
dependencies' replayed lints, which are not ours to fix. -/
abbrev strict : Array LeanOption := #[⟨`warningAsError, true⟩]

package atoi_radix10_verification

/-- Generated from the crate by `earthly +extract`; never edit by hand. -/
lean_lib AtoiRadix10 where
  leanOptions := strict

@[default_target] lean_lib Proofs where
  leanOptions := strict

/-- Fails the build if a headline theorem picks up an axiom beyond Lean's standard three. -/
@[default_target] lean_lib Audit where
  leanOptions := strict
