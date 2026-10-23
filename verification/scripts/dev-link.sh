#!/usr/bin/env bash
# Points `.aeneas` at a local checkout of the Aeneas fork's Lean backend, for editing proofs
# outside the container: `scripts/dev-link.sh ~/git/gilescope/aeneas`. The checkout must be
# built (`lake exe cache get && lake build Aeneas` in its backends/lean) and on the same Lean
# as ./lean-toolchain. The Earthfile's `+prove` is the check that counts.
set -euo pipefail
cd "$(dirname "$0")/.."
backend="${1:?usage: dev-link.sh <aeneas-checkout>}/backends/lean"
[ -f "$backend/lean-toolchain" ] || { echo "no Lean backend at $backend" >&2; exit 1; }
cmp -s lean-toolchain "$backend/lean-toolchain" || {
  echo "Lean mismatch: $(cat lean-toolchain) here, $(cat "$backend/lean-toolchain") in $backend" >&2; exit 1; }
ln -sfn "$backend" .aeneas
echo ".aeneas -> $backend"
