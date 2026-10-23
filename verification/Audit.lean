import Proofs

/-!
Axiom audit, run by `lake build`: every headline theorem rests only on Lean's three standard
axioms - no `sorry`, no `native_decide`/`bv_decide` (`Lean.ofReduceBool`), no Aeneas axioms.
-/

open atoi_radix10

/-- info: 'atoi_radix10.load.load_u64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms load.load_u64_spec

/-- info: 'atoi_radix10.parse_2_chars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_2_chars_spec

/-- info: 'atoi_radix10.parse_4_chars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_4_chars_spec

/-- info: 'atoi_radix10.parse_8_chars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_8_chars_spec

/-- info: 'atoi_radix10.parse_16_chars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_16_chars_spec

/-- info: 'atoi_radix10.parse_32_chars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_32_chars_spec
