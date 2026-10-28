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

/-- info: 'atoi_radix10.faithful_u8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_u8

/-- info: 'atoi_radix10.parse_loop1_loop0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop1_loop0_spec

/-- info: 'atoi_radix10.parse_loop0_loop0_loop1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop0_loop0_loop1_spec

/-- info: 'atoi_radix10.parse_loop1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop1_spec

/-- info: 'atoi_radix10.parse_loop2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop2_spec

/-- info: 'atoi_radix10.chunk32_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chunk32_spec

/-- info: 'atoi_radix10.parse_loop0_loop0_loop0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop0_loop0_loop0_spec

/-- info: 'atoi_radix10.parse_loop0_loop0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop0_loop0_spec

/-- info: 'atoi_radix10.parse_loop0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_loop0_spec

/-- info: 'atoi_radix10.parse_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec

/-- info: 'atoi_radix10.parse_spec_u8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_u8

/-- info: 'atoi_radix10.faithful_u16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_u16

/-- info: 'atoi_radix10.parse_spec_u16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_u16

/-- info: 'atoi_radix10.faithful_u32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_u32

/-- info: 'atoi_radix10.parse_spec_u32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_u32

/-- info: 'atoi_radix10.faithful_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_u64

/-- info: 'atoi_radix10.parse_spec_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_u64

/-- info: 'atoi_radix10.faithful_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_u128

/-- info: 'atoi_radix10.parse_spec_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_u128

/-- info: 'atoi_radix10.faithful_i8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_i8

/-- info: 'atoi_radix10.parse_spec_i8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_i8

/-- info: 'atoi_radix10.faithful_i16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_i16

/-- info: 'atoi_radix10.parse_spec_i16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_i16

/-- info: 'atoi_radix10.faithful_i32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_i32

/-- info: 'atoi_radix10.parse_spec_i32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_i32

/-- info: 'atoi_radix10.faithful_i64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_i64

/-- info: 'atoi_radix10.parse_spec_i64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_i64

/-- info: 'atoi_radix10.faithful_i128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faithful_i128

/-- info: 'atoi_radix10.parse_spec_i128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_spec_i128
