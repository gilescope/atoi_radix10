import Proofs.NegChunks

/-!
The negative SWAR block of `parse` (`src/parse.rs` lines 372-502, `parse_inner_loop0_loop0_loop0`),
chunk by chunk, against the negative fold. Its lifted `return`s come back in the 22 slots.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The post-condition of the negative first block: its `inr` also carries the range, unchanged. -/
def NegBlockPost1 {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 D : List U8) (M : ℕ) {A I : Type}
    (it : I) : Sum (Sum A (NegExit T)) (Slice U8 × T × I) → Prop
  | .inl (.inl _) => False
  | .inl (.inr (_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, _, _, _, _, _)) =>
    SlotsOK (NegResult toInt lo hi D0) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22]
  | .inr (s', res', i) => NegBlockInv toInt D s' res' ∧ s'.val.length < M ∧ i = it

/-- The post-condition of the first block's inner conditional: the single-digit exit, or the
range handed on with the fact that this was not the single-digit case. -/
def NegFirstPost {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 : List U8) {A I : Type} (it : I)
    (notOne : Prop) : Sum (Sum A (NegExit T)) I → Prop
  | .inl (.inl _) => False
  | .inl (.inr (_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, _, _, _, _, _)) =>
    SlotsOK (NegResult toInt lo hi D0) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22]
  | .inr r => r = it ∧ notOne

/-- A negative chunk block, proved in place: `N` bytes of `D` read by the parser `hp` and
converted by `hFW`, from the state `hinv` with `hN` bytes at hand; the goal's own bound on what
remains is discharged by `omega` from the context. -/
syntax "negchunk " num term:max term:max term:max ident ident ident ident ident ident ident ident : tactic
macro_rules
  | `(tactic| negchunk $N $hp $hFW $D $hF $hlo $hH $ch $t $ht $hinv $hN) => `(tactic| (
      obtain ⟨k, hk, hs5, hallk, hres1⟩ := $hinv
      have hlen5 := congrArg List.length hs5
      simp only [List.length_drop] at hlen5
      have hDlt := ($hH).len_lt
      have hSub := ($hF).sub
      have hMul := ($hF).mul
      have hTR := ($hF).TREE
      have hFW' := $hFW
      have hSC := ($hF).sub_checked
      have hEq := ($hF).eq
      have hTL := ($hF).TAIL
      have hFS := ($hF).FIRST_SIG
      step with $hp _ $hN as ⟨r, hr⟩
      step as ⟨cf, hcf⟩
      rcases r with v | e
      · simp only at hr hcf
        subst hcf
        first
          | (have hNd := (allDigits_take_two _ $hN).mpr ⟨hr.1, hr.2.1⟩
             have hv := hr.2.2
             rw [hs5] at hNd hv)
          | (have hNd := hr.1
             have hv := hr.2
             rw [hs5] at hNd hv)
        have hv' := congrArg (Nat.cast (R := ℤ)) hv
        obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
          chunk_step_neg $hF $hlo $D hDlt k $N (by omega) hallk hNd (v.val : ℤ) hv'
        step as ⟨val3, hval3⟩
        have hval3' := hval3 hvhi
        step as ⟨s9, hs9, hs9len⟩
        have hs9' := hs9
        rw [hs5, drop_drop_val] at hs9'
        step as ⟨b2, hb2⟩
        split
        · rename_i hb2t
          have hempty : k + $N = ($D).length := by
            have h9z : (↑s9 : List U8) = [] := by
              have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
            rw [hs9', List.drop_eq_nil_iff] at h9z; omega
          have h0 : ($D).length - (k + $N) = 0 := by omega
          rw [h0, pow_zero, one_mul] at har
          rw [← hres1, ← hval3'] at har
          step with hSub _ val3 har as ⟨res2, hres2⟩
          have hres2' := hfull hempty
          rw [← hres1, ← hval3', ← hres2] at hres2'
          have hallD := hall'
          rw [hempty, List.take_length] at hallD
          revert $hH:ident
          rcases hck : $ch:ident with _ | ⟨d, ct⟩ <;> intro $hH:ident <;> dsimp only
          · rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) (final_neg_unchecked $hF $hlo $hH hallD res2 hres2') (by simp)
          · step as ⟨tl, htl⟩
            step as ⟨b3, hb3⟩
            split
            · rename_i hb3t
              have heq := hb3
              rw [hb3t] at heq
              simp at heq
              step as ⟨fs, hfs⟩
              split
              · rename_i hdfs
                rw [WP.spec_ok]
                exact SlotsOK_of_mem (by simp)
                  (final_neg_tail $hF $hH hallD res2 hres2' tl $t (htl $hlo) $ht heq (by rw [hdfs]; exact hfs)) (by simp)
              · step as ⟨o1, ho1⟩
                apply WP.spec_bind (final_neg_checked $hF $hH hallD res2 hres2' o1 ho1)
                intro r1 hr1
                rw [WP.spec_ok]
                exact SlotsOK_of_mem (by simp) hr1 (by simp)
            · step as ⟨o1, ho1⟩
              apply WP.spec_bind (final_neg_checked $hF $hH hallD res2 hres2' o1 ho1)
              intro r1 hr1
              rw [WP.spec_ok]
              exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨tr, htrlen, htr⟩
          have hs9l : s9.len.val = (↑s9 : List U8).length := Slice.len_val s9
          rw [hs9', List.length_drop] at hs9l
          step with Slice.index_usize_spec tr s9.len
            (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
          have htv := htr s9.len.val (by rw [hs9l, htrlen]; omega)
          rw [← htt, hs9l] at htv
          have hmr' := hmr
          rw [← htv, ← hval3'] at hmr'
          step with hMul tt val3 hmr' as ⟨t2, ht2⟩
          have hsub' := har
          rw [← hres1, ← htv, ← hval3', ← ht2] at hsub'
          step with hSub _ t2 hsub' as ⟨res2, hres2⟩
          have hb2f : ¬ b2 = true := by assumption
          have hkN : k + $N < ($D).length := by
            have h0 : ¬ (↑s9 : List U8).length = 0 := by
              intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
            rw [hs9', List.length_drop] at h0; omega
          refine ⟨⟨k + $N, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
          rw [hs9', List.length_drop]; omega
      · simp only at hr hcf
        subst hcf
        obtain ⟨hnd, hkind⟩ := hr
        have hnot : ¬ allDigits $D := by
          intro hall
          apply hnd
          first
            | (rw [hs5]; exact allDigits_take (allDigits_drop hall k) $N)
            | (rw [← allDigits_take_two _ $hN, hs5]; exact allDigits_take (allDigits_drop hall k) $N)
        step as ⟨r1, hr1⟩
        subst hr1
        exact SlotsOK_of_mem (by simp) (final_neg_invalid $hF $hH hnot e hkind) (by simp)))

/-- A negative chunk guarded by the alignment test. -/
syntax "nguarded " num term:max term:max term:max ident ident ident ident ident ident ident ident : tactic
macro_rules
  | `(tactic| nguarded $N $hp $hFW $D $hF $hlo $hH $ch $t $ht $hinv $hN) => `(tactic| (
      refine WP.spec_ite (fun _ => ?_) (fun _ => ?_)
      · negchunk $N $hp $hFW $D $hF $hlo $hH $ch $t $ht $hinv $hN
      · refine (WP.spec_ok _).mpr ?_
        exact ⟨$hinv, by omega⟩))

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
theorem parse_inner_loop0_loop0_loop0_spec {T : Type} {inst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful inst toInt lo hi c) (hlo : lo < 0)
    (D0 : List U8) (t : T) (ht : toInt t = lo) (s : Slice U8) (is_signed_ty : Bool)
    (checked : Option (U8 × T)) (val val1 : U8) (l : Usize) (res : T) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hH : NegHandover toInt lo hi c D0 s.val checked)
    (hres : toInt res = 0) (hl : l.val = s.val.length) :
    parse.parse_inner_loop0_loop0_loop0 inst t { start := 0#i32, «end» := 1#i32 } s is_signed_ty
        checked val val1 l res i s1 s2 s3 s4
      ⦃ (out : NegExit T) => match out with
        | (_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, _, _, _, _, _) => SlotsOK (NegResult toInt lo hi D0) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22] ⦄ := by
  unfold parse.parse_inner_loop0_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : core.ops.range.Range I32 × Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Usize × T ×
        U8 × Slice U8 × Slice U8 × Slice U8 × Slice U8) => (p.1.«end».val - p.1.start.val).toNat)
    (fun (p : core.ops.range.Range I32 × Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Usize × T ×
        U8 × Slice U8 × Slice U8 × Slice U8 × Slice U8) =>
      match p with
      | (iter, s', b, ch, v, v1', l', res', i', t1, t2, t3, t4) =>
        ch = checked ∧ l'.val = s.val.length ∧ iter.«end».val = 1 ∧
        ((iter.start.val = 0 ∧ s' = s ∧ toInt res' = 0) ∨
         (iter.start.val = 1 ∧ allDigits s.val ∧ toInt res' = -(decimal s.val : ℤ))))
  · rintro ⟨iter, s', b, ch, v, v1', l', res', i', t1, t2, t3, t4⟩ ⟨rfl, hl', hend, hcase⟩
    have hSub := hF.sub
    have hMul := hF.mul
    have hTR := hF.TREE
    have hF8 := hF.from_u8
    have hSC := hF.sub_checked
    have hEq := hF.eq
    have hTL := hF.TAIL
    have hFS := hF.FIRST_SIG
    have hBITS := hF.BITS
    have hc3 := hF.three_le_c
    unfold parse.parse_inner_loop0_loop0_loop0.body
    step as ⟨o, iter1, hnext, hend1⟩
    rcases hcase with ⟨hstart, rfl, hres'⟩ | ⟨hstart, hall, hres'⟩
    · -- first iteration: the block
      rw [hstart, hend] at hnext
      simp only [show (0 : ℤ) < 1 from by norm_num, ite_true] at hnext
      obtain ⟨rfl, hstart1⟩ := hnext
      step*
      have hDlt := hH.len_lt
      have hDpos := hH.len_pos
      refine WP.spec_bind (Pₘ := NegBlockPost1 toInt lo hi D0 (↑s' : List U8) ((↑s' : List U8).length + 1) iter1) ?_ ?_
      · -- the first block: one byte, when the slice is odd for `u16`
        refine WP.spec_ite (fun hb => ?_) (fun hb => ?_)
        · step with Slice.index_usize_spec s' 0#usize (by simp [Slice.length]; omega) as ⟨d, hd⟩
          have hd0 : (↑s' : List U8)[0]? = some d := by rw [hd]; exact List.getElem?_eq_getElem _
          have hcons := cons_of_getElem?_zero _ hd0
          step as ⟨val2, hval2⟩
          have hw := U8.wrapping_sub_48_val d
          have hvb := U8.val_lt_256 d
          have hdig := wrapping_digit_test d.val hvb
          refine WP.spec_bind (Pₘ := NegFirstPost toInt lo hi D0 iter1 (¬ (val2 ≤ 9#u8 ∧ l' = 1#usize))) ?_ ?_
          · refine WP.spec_ite (fun h9 => ?_) (fun h9 => ?_)
            · refine WP.spec_ite (fun hl1 => ?_) (fun hl1 => ?_)
              · -- a single digit: the whole number
                have h9v : val2.val ≤ 9 := by
                  have := (UScalar.le_equiv val2 9#u8).mp h9; simpa using this
                rw [hval2, hw] at h9v
                have hdg : isDigit d := by show 48 ≤ d.val ∧ d.val ≤ 57; omega
                have hlen1 : (↑s' : List U8).length = 1 := by
                  have := congrArg UScalar.val hl1; simp at this; omega
                have hD : (↑s' : List U8) = [d] := by
                  rw [hcons]; congr 1; rw [← List.length_eq_zero_iff]; simp [hlen1]
                have hchn : ch = none := by
                  rcases hck : ch with _ | ⟨d', ct⟩
                  · rfl
                  · exfalso
                    obtain ⟨_, _, ⟨a, _, _, _, _, _, hs⟩, _⟩ := hH
                    have := (hs d' ct hck).2.2; omega
                subst hchn
                step as ⟨t1, ht1⟩
                have hd9 : (d.val : ℤ) - 48 ≤ 9 := by omega
                have hv2 : (val2.val : ℤ) = (d.val : ℤ) - 48 := by rw [hval2, hw]; omega
                have ht1' : toInt t1 = (d.val : ℤ) - 48 := by rw [ht1 (by have := hF.hi_ge; have : (10:ℤ)^1 ≤ 10^(c-1) := pow_le_pow_right₀ (by norm_num) (by omega); omega), hv2]
                have hsub : InRange lo hi (toInt res' - toInt t1) := by
                  rw [hres', ht1']; have := hF.signed hlo; have := hF.hi_ge
                  have : (10:ℤ)^1 ≤ 10^(c-1) := pow_le_pow_right₀ (by norm_num) (by omega)
                  constructor <;> omega
                step with hSub res' t1 hsub as ⟨res1, hres1⟩
                have hres1' : toInt res1 = -(decimal (↑s' : List U8) : ℤ) := by
                  rw [hres1, hres', ht1', hD]; simp [decimal]; have := hdg.1; omega
                have hallD : allDigits (↑s' : List U8) := by rw [hD]; simp [allDigits, hdg]
                exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res1 hres1') (by simp)
              · refine (WP.spec_ok _).mpr ?_
                exact ⟨rfl, fun h => hl1 h.2⟩
            · refine (WP.spec_ok _).mpr ?_
              exact ⟨rfl, fun h => h9 h.1⟩
          · rintro s6 hs6
            rcases s6 with (c' | b1) | r
            · exact (hs6 : False).elim
            · rcases b1 with ⟨a1, a2, a3, a4, a5, a6, a7, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, a8, a9, a10, a11, a12⟩
              exact (WP.spec_ok _).mpr hs6
            · obtain ⟨rfl, hnot1⟩ := hs6
              dsimp only
              refine WP.spec_ite (fun h9 => ?_) (fun h9 => ?_)
              · -- a digit, with more to come: weight it
                have h9v : val2.val ≤ 9 := by
                  have := (UScalar.le_equiv val2 9#u8).mp h9; simpa using this
                rw [hval2, hw] at h9v
                have hdg : isDigit d := by show 48 ≤ d.val ∧ d.val ≤ 57; omega
                have hlen2 : 2 ≤ (↑s' : List U8).length := by
                  have hne : ¬ l' = 1#usize := fun h => hnot1 ⟨h9, h⟩
                  have : l'.val ≠ 1 := fun h => hne (UScalar.eq_of_val_eq (by rw [h]; simp))
                  omega
                have hN : allDigits (((↑s' : List U8).drop 0).take 1) := by
                  rw [List.drop_zero, hcons]; simp [allDigits, hdg]
                have hv2 : (val2.val : ℤ) = (d.val : ℤ) - 48 := by rw [hval2, hw]; omega
                have hv : (val2.val : ℤ) = (decimal (((↑s' : List U8).drop 0).take 1) : ℤ) := by
                  rw [List.drop_zero, hcons, hv2]; simp [decimal]; have := hdg.1; omega
                obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
                  chunk_step_neg hF hlo (↑s' : List U8) hDlt 0 1 (by omega) (by simp [allDigits]) hN _ hv
                step as ⟨t1, ht1⟩
                have ht1' : toInt t1 = (val2.val : ℤ) := ht1 hvhi
                have hsub : InRange lo hi (toInt res' - toInt t1) := by
                  rw [hres', ht1']; have := hF.signed hlo; constructor <;> omega
                step with hSub res' t1 hsub as ⟨res1, hres1⟩
                step as ⟨s7, hs7, hs7len⟩
                have hs7' : (↑s7 : List U8) = (↑s' : List U8).drop (0 + 1) := by rw [hs7]
                step as ⟨tr, htrlen, htr⟩
                have hs7l : s7.len.val = (↑s' : List U8).length - (0 + 1) := by
                  rw [Slice.len_val]; simp [Slice.length, hs7']
                step with Slice.index_usize_spec tr s7.len
                  (by rw [hs7l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨t2, ht2⟩
                have htv : toInt t2 = 10 ^ ((↑s' : List U8).length - (0 + 1)) := by
                  rw [ht2]; simp only [hs7l]; exact htr _ (by omega)
                have hd0' : decimal ([] : List U8) = 0 := rfl
                have hmr' : InRange lo hi (toInt res1 * toInt t2) := by
                  rw [hres1, hres', ht1', htv]
                  have := har; simp only [List.take_zero, hd0', Nat.cast_zero, zero_mul, neg_zero, zero_sub] at this
                  rw [show (0 - (val2.val : ℤ)) * 10 ^ ((↑s' : List U8).length - (0 + 1)) =
                    -(10 ^ ((↑s' : List U8).length - (0 + 1)) * (val2.val : ℤ)) by ring]
                  exact this
                step with hMul res1 t2 hmr' as ⟨res2, hres2⟩
                refine ⟨⟨0 + 1, by omega, hs7', hall', ?_⟩, by rw [hs7', List.length_drop]; omega, rfl⟩
                rw [hres2, hres1, hres', ht1', htv, ← hresnew]
                simp only [List.take_zero, hd0', Nat.cast_zero, zero_mul, neg_zero, zero_sub]
                ring
              · -- not a digit
                have h9v : 9 < val2.val := by
                  have := mt (UScalar.le_equiv val2 9#u8).mpr h9; simp at this; omega
                rw [hval2, hw] at h9v
                have hnd : ¬ isDigit d := by show ¬ (48 ≤ d.val ∧ d.val ≤ 57); omega
                have hnot : ¬ allDigits (↑s' : List U8) := by
                  intro hall; exact hnd (hall d (by rw [hcons]; simp))
                rw [WP.spec_ok]
                exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot _ rfl) (by simp)
        · -- aligned already: nothing consumed yet
          refine (WP.spec_ok _).mpr ?_
          exact ⟨⟨0, hDpos, by simp, by simp [allDigits], by simp [hres', decimal]⟩, by omega, rfl⟩
      · -- the join after the first block
        rintro s5 hs5
        rcases s5 with (c' | b1) | ⟨s5, res1, iter2⟩
        · exact (hs5 : False).elim
        · rcases b1 with ⟨a1, a2, a3, a4, a5, a6, a7, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, a8, a9, a10, a11, a12⟩
          exact (WP.spec_ok _).mpr hs5
        · dsimp only
          obtain ⟨hinv5, hlen5, rfl⟩ := hs5
          -- level 2: at least two bytes remain and the type has 8 bits; afterwards fewer than two
          refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
          · refine WP.spec_ite (fun hg2 => ?_) (fun hg2 => ?_)
            · have h2 := len_ge_of_guard (N := 2) s5 2#usize (by simp) hg2
              step as ⟨i1, hi1, hcases⟩
              obtain ⟨hc16, hc32, hc64, hc128, hc39⟩ := c_le_of_bits hF i1.val hi1 hcases
              refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
              · refine WP.spec_ite (fun hb8 => ?_) (fun hb8 => ?_)
                · step as ⟨b1⟩
                  refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) ((↑s5 : List U8).length + 1)) ?_ ?_
                  · nguarded 2 parse_2_chars_spec hF.from_u16 (↑s' : List U8) hF hlo hH ch t ht hinv5 h2
                  · join s9 res2 hs8
                    obtain ⟨hinv9, hlen9⟩ := hs8
                    -- level 4: afterwards fewer than four
                    refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                    · refine WP.spec_ite (fun hg4 => ?_) (fun hg4 => ?_)
                      · have h4 := len_ge_of_guard (N := 4) s9 4#usize (by simp) hg4
                        refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                        · refine WP.spec_ite (fun hb16 => ?_) (fun hb16 => ?_)
                          · step as ⟨b2⟩
                            refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) ((↑s9 : List U8).length + 1)) ?_ ?_
                            · nguarded 4 parse_4_chars_spec hF.from_u16 (↑s' : List U8) hF hlo hH ch t ht hinv9 h4
                            · join s13 res3 hs12
                              obtain ⟨hinv13, hlen13⟩ := hs12
                              -- level 8: afterwards fewer than eight
                              refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                              · refine WP.spec_ite (fun hg8 => ?_) (fun hg8 => ?_)
                                · have h8 := len_ge_of_guard (N := 8) s13 8#usize (by simp) hg8
                                  refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                                  · refine WP.spec_ite (fun hb32 => ?_) (fun hb32 => ?_)
                                    · step as ⟨b3⟩
                                      refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) ((↑s13 : List U8).length + 1)) ?_ ?_
                                      · nguarded 8 parse_8_chars_spec hF.from_u32 (↑s' : List U8) hF hlo hH ch t ht hinv13 h8
                                      · join s17 res4 hs16
                                        obtain ⟨hinv17, hlen17⟩ := hs16
                                        -- level 16: afterwards fewer than sixteen
                                        refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                        · refine WP.spec_ite (fun hg16 => ?_) (fun hg16 => ?_)
                                          · have h16 := len_ge_of_guard (N := 16) s17 16#usize (by simp) hg16
                                            refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                            · refine WP.spec_ite (fun hb64 => ?_) (fun hb64 => ?_)
                                              · step as ⟨b4⟩
                                                refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) ((↑s17 : List U8).length + 1)) ?_ ?_
                                                · nguarded 16 parse_16_chars_spec hF.from_u64 (↑s' : List U8) hF hlo hH ch t ht hinv17 h16
                                                · join s21 res5 hs20
                                                  obtain ⟨hinv21, hlen21⟩ := hs20
                                                  -- level 32: afterwards fewer than 32
                                                  refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 32) ?_ ?_
                                                  · refine WP.spec_ite (fun hg32 => ?_) (fun hg32 => ?_)
                                                    · have h32 := len_ge_of_guard (N := 32) s21 32#usize (by simp) hg32
                                                      refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 32) ?_ ?_
                                                      · refine WP.spec_ite (fun hb128 => ?_) (fun hb128 => ?_)
                                                        · negchunk 32 parse_32_chars_spec hF.from_u128 (↑s' : List U8) hF hlo hH ch t ht hinv21 h32
                                                        · -- fewer than 128 bits: at most 20 digits, so fewer than 32 bytes
                                                          exfalso
                                                          have hb : i1.val < 128 := by
                                                            have := mt (UScalar.le_equiv 128#u32 i1).mpr hb128; simp at this; omega
                                                          have := hc128 hb; have := hDlt
                                                          obtain ⟨k, hk, hs21v, _, _⟩ := hinv21
                                                          rw [hs21v, List.length_drop] at h32; omega
                                                      · join s23 res6 hs22
                                                    · okpost ⟨hinv21, by
                                                        have := mt (UScalar.le_equiv 32#usize s21.len).mpr hg32
                                                        simp at this; omega⟩
                                                  · join s23 res6 hs22
                                                    obtain ⟨hinv23, hlen23⟩ := hs22
                                                    -- the aligned sixteen: afterwards fewer than sixteen
                                                    refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 16) ?_ ?_
                                                    · refine WP.spec_ite (fun hg16b => ?_) (fun hg16b => ?_)
                                                      · have hNb := len_ge_of_guard (N := 16) s23 16#usize (by simp) hg16b
                                                        negchunk 16 parse_16_chars_spec hF.from_u64 (↑s' : List U8) hF hlo hH ch t ht hinv23 hNb
                                                      · okpost ⟨hinv23, by
                                                          have := mt (UScalar.le_equiv 16#usize s23.len).mpr hg16b
                                                          simp at this; omega⟩
                                                    · join s25 res7 hs24
                                              · -- fewer than 64 bits: at most 10 digits
                                                exfalso
                                                have hb : i1.val < 64 := by
                                                  have := mt (UScalar.le_equiv 64#u32 i1).mpr hb64; simp at this; omega
                                                have := hc64 hb; have := hDlt
                                                obtain ⟨k, hk, hs17v, _, _⟩ := hinv17
                                                rw [hs17v, List.length_drop] at h16; omega
                                            · join s19 res5 hs18
                                          · okpost ⟨hinv17, by
                                              have := mt (UScalar.le_equiv 16#usize s17.len).mpr hg16
                                              simp at this; omega⟩
                                        · join s19 res5 hs18
                                          obtain ⟨hinv19, hlen19⟩ := hs18
                                          -- the aligned eight: afterwards fewer than eight
                                          refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 8) ?_ ?_
                                          · refine WP.spec_ite (fun hg8b => ?_) (fun hg8b => ?_)
                                            · have hNb := len_ge_of_guard (N := 8) s19 8#usize (by simp) hg8b
                                              negchunk 8 parse_8_chars_spec hF.from_u32 (↑s' : List U8) hF hlo hH ch t ht hinv19 hNb
                                            · okpost ⟨hinv19, by
                                                have := mt (UScalar.le_equiv 8#usize s19.len).mpr hg8b
                                                simp at this; omega⟩
                                          · join s21 res6 hs20
                                    · -- fewer than 32 bits: at most 5 digits
                                      exfalso
                                      have hb : i1.val < 32 := by
                                        have := mt (UScalar.le_equiv 32#u32 i1).mpr hb32; simp at this; omega
                                      have := hc32 hb; have := hDlt
                                      obtain ⟨k, hk, hs13v, _, _⟩ := hinv13
                                      rw [hs13v, List.length_drop] at h8; omega
                                  · join s15 res4 hs14
                                · okpost ⟨hinv13, by
                                    have := mt (UScalar.le_equiv 8#usize s13.len).mpr hg8
                                    simp at this; omega⟩
                              · join s15 res4 hs14
                                obtain ⟨hinv15, hlen15⟩ := hs14
                                -- the aligned four: afterwards fewer than four
                                refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 4) ?_ ?_
                                · refine WP.spec_ite (fun hg4b => ?_) (fun hg4b => ?_)
                                  · have hNb := len_ge_of_guard (N := 4) s15 4#usize (by simp) hg4b
                                    negchunk 4 parse_4_chars_spec hF.from_u16 (↑s' : List U8) hF hlo hH ch t ht hinv15 hNb
                                  · okpost ⟨hinv15, by
                                      have := mt (UScalar.le_equiv 4#usize s15.len).mpr hg4b
                                      simp at this; omega⟩
                                · join s17 res5 hs16
                          · -- fewer than 16 bits: at most 3 digits
                            exfalso
                            have hb : i1.val < 16 := by
                              have := mt (UScalar.le_equiv 16#u32 i1).mpr hb16; simp at this; omega
                            have := hc16 hb; have := hDlt
                            obtain ⟨k, hk, hs9v, _, _⟩ := hinv9
                            rw [hs9v, List.length_drop] at h4; omega
                        · join s11 res3 hs10
                      · okpost ⟨hinv9, by
                          have := mt (UScalar.le_equiv 4#usize s9.len).mpr hg4
                          simp at this; omega⟩
                    · join s11 res3 hs10
                      obtain ⟨hinv11, hlen11⟩ := hs10
                      -- the aligned pair: afterwards fewer than two
                      refine WP.spec_bind (Pₘ := NegBlockPost toInt lo hi D0 (↑s' : List U8) 2) ?_ ?_
                      · refine WP.spec_ite (fun hg2b => ?_) (fun hg2b => ?_)
                        · have hNb := len_ge_of_guard (N := 2) s11 2#usize (by simp) hg2b
                          negchunk 2 parse_2_chars_spec hF.from_u16 (↑s' : List U8) hF hlo hH ch t ht hinv11 hNb
                        · okpost ⟨hinv11, by
                            have := mt (UScalar.le_equiv 2#usize s11.len).mpr hg2b
                            simp at this; omega⟩
                      · join s13 res4 hs12
                · -- fewer than 8 bits: no such type
                  exfalso
                  have hb : i1.val < 8 := by
                    have := mt (UScalar.le_equiv 8#u32 i1).mpr hb8; simp at this; omega
                  rcases hcases with h | h | h | h | h <;> omega
              · join s7 res2 hs6
            · okpost ⟨hinv5, by
                have := mt (UScalar.le_equiv 2#usize s5.len).mpr hg2
                simp at this; omega⟩
          · join s7 res2 hs6
            dsimp only
            -- the tail: exactly one byte is left
            obtain ⟨⟨k, hk, hs7, hallk, hres2⟩, hlen7⟩ := hs6
            have hk1 : k + 1 = (↑s' : List U8).length := by
              rw [hs7, List.length_drop] at hlen7; omega
            step as ⟨o1, ho1⟩
            rcases o1 with _ | val2
            · exfalso
              have : (↑s7 : List U8) ≠ [] := by
                rw [hs7]; intro h; rw [List.drop_eq_nil_iff] at h; omega
              exact this (List.head?_eq_none_iff.mp ho1.symm)
            · have hhead : (↑s7 : List U8).head? = some val2 := ho1.symm
              have hcons7 : (↑s7 : List U8) = val2 :: (↑s7 : List U8).tail := by
                apply cons_of_getElem?_zero
                rcases h : (↑s7 : List U8) with _ | ⟨a, l⟩
                · rw [h] at hhead; simp at hhead
                · rw [h] at hhead; simpa using hhead
              have hval2 : ((↑s' : List U8).drop k).take 1 = [val2] := by
                rw [← hs7, hcons7]; simp
              step as ⟨val3, hval3⟩
              have hw := U8.wrapping_sub_48_val val2
              have hvb := U8.val_lt_256 val2
              have hdig := wrapping_digit_test val2.val hvb
              refine WP.spec_ite (fun hgt => ?_) (fun hle => ?_)
              · -- not a digit
                have h9 : 9 < val3.val := by have := UScalar.lt_equiv 9#u8 val3 |>.mp hgt; simpa using this
                rw [hval3, hw] at h9
                have hnd : ¬ isDigit val2 := by show ¬ (48 ≤ val2.val ∧ val2.val ≤ 57); omega
                have hnot : ¬ allDigits (↑s' : List U8) := by
                  intro hall
                  apply hnd
                  have := allDigits_drop hall k
                  rw [← hs7, hcons7] at this
                  exact this val2 (by simp)
                rw [WP.spec_ok]
                exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot _ rfl) (by simp)
              · -- a digit: the last one
                have h9 : val3.val ≤ 9 := by
                  have := mt (UScalar.lt_equiv 9#u8 val3).mpr hle; simp at this; omega
                rw [hval3, hw] at h9
                have hdg : isDigit val2 := by show 48 ≤ val2.val ∧ val2.val ≤ 57; omega
                have hN : allDigits (((↑s' : List U8).drop k).take 1) := by
                  rw [hval2]; simp [allDigits, hdg]
                have hv : (val3.val : ℤ) = (decimal (((↑s' : List U8).drop k).take 1) : ℤ) := by
                  rw [hval2, hval3, hw]; simp [decimal]; omega
                obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
                  chunk_step_neg hF hlo (↑s' : List U8) hDlt k 1 (by omega) hallk hN _ hv
                step as ⟨tt, htt⟩
                have htt' : toInt tt = (val3.val : ℤ) := htt hvhi
                have hsub : InRange lo hi (toInt res2 - toInt tt) := by
                  rw [hres2, htt', hfull hk1]
                  have := hF.signed hlo
                  have hp : (0 : ℤ) ≤ (decimal (↑s' : List U8) : ℤ) := by positivity
                  obtain ⟨_, hdhi⟩ := decimal_take_lt_hi hF _ (by have := hall'; rwa [hk1, List.take_length] at this) hDlt
                  constructor <;> omega
                step with hSub res2 tt hsub as ⟨res3, hres3⟩
                refine ⟨?_, ?_, Or.inr ⟨by omega, ?_, ?_⟩, ?_⟩
                · exact hl'
                · rw [hend1, hend]
                · have := hall'; rwa [hk1, List.take_length] at this
                · rw [hres3, hres2, htt']; exact hfull hk1
                · rw [hend1, hend, hstart1, hstart]; simp
    · -- second iteration: the range is exhausted, return
      rw [hstart, hend] at hnext
      simp only [lt_irrefl, ite_false] at hnext
      obtain ⟨rfl, _⟩ := hnext
      revert hH
      rcases hck : ch with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hall res' hres') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        refine WP.spec_ite (fun hb3t => ?_) (fun hb3f => ?_)
        · have heq : toInt res' = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          refine WP.spec_ite (fun hdfs => ?_) (fun hdfs => ?_)
          · rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hall res' hres' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hall res' hres' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hall res' hres' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
  · exact ⟨rfl, hl, by simp, Or.inl ⟨by simp, rfl, hres⟩⟩

end atoi_radix10
