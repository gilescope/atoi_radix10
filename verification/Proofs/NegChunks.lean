import Proofs.NegBlock

/-!
The chunk blocks of the negative SWAR block (`src/parse.rs` lines 388-485), one lemma each,
stated on the extracted code verbatim: the chunk's digits are subtracted from `res` at the
weight of what remains; a non-digit fills a result slot with `InvalidDigit`; a chunk that ends
the bytes fills a slot with the final answer, checked against the digit set aside.
-/

open Aeneas Aeneas.Std Result

namespace atoi_radix10

/-- The negative `for` body's own `cont` payload. -/
abbrev NegCont (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Usize × T ×
  core.ops.range.Range I32 × U8 × Slice U8 × Slice U8 × Slice U8 × Slice U8
/-- One lifted `return`. -/
abbrev Slot (T : Type) := Option (core.result.Result T ParseIntErrorPublic)
/-- A lifted exit's payload: the state, the 22 result slots, and the slices that ride along. -/
abbrev NegExit (T : Type) := Slice U8 × Bool × Option (U8 × T) × U8 × U8 × Usize × T ×
  Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × Slot T × U8 × Slice U8 × Slice U8 × Slice U8 × Slice U8
/-- What a negative chunk block hands on. -/
abbrev NegJoin (T : Type) := Sum (Sum (NegCont T) (NegExit T)) (Slice U8 × T)

/-- The post-condition of a negative chunk block: an exit fills a slot rightly; a state handed on
is inside the invariant with fewer than `M` bytes left. -/
def NegBlockPost {T : Type} (toInt : T → ℤ) (lo hi : ℤ) (D0 D : List U8) (M : ℕ) {A : Type} :
    Sum (Sum A (NegExit T)) (Slice U8 × T) → Prop
  | .inl (.inl _) => False
  | .inl (.inr (_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, _, _, _, _, _)) =>
    SlotsOK (NegResult toInt lo hi D0) [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22]
  | .inr (s', res') => NegBlockInv toInt D s' res' ∧ s'.val.length < M

theorem NegBlockPost.mono {T : Type} {toInt : T → ℤ} {lo hi : ℤ} {D0 D : List U8} {M M' : ℕ}
    {A : Type} (h : M ≤ M') (x : Sum (Sum A (NegExit T)) (Slice U8 × T))
    (hx : NegBlockPost toInt lo hi D0 D M x) : NegBlockPost toInt lo hi D0 D M' x := by
  rcases x with (c | ⟨_, _, _, _, _, _, _, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, _, _, _, _, _⟩) | ⟨s', res'⟩
  · exact hx
  · exact hx
  · exact ⟨hx.1, by have := hx.2; omega⟩

/-- The 2-byte chunk at `s6`. -/
theorem negchunk2_s6_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s6 : Slice U8) (res1 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s6 res1) (hN : 2 ≤ s6.val.length) :
    (
      do
      let r ← parse_2_chars s6
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let val3 ← FromStrRadixHelperInst.from_u16 val2
        let s10 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 2#usize } s6
        let b2 : Bool ← core.slice.Slice.is_empty s10
        if b2
        then
          let res2 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub res1
              val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl (_root_.Sum.inr (s10, is_signed_ty,
              none, val, val1, l, res2, none, none, none, none,
              some (core.result.Result.Ok res2), none, none, none,
              none, none, none, none, none, none, none, none, none,
              none, none, none, none, none, i, s1, s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ← FromStrRadixHelperInst.TAIL
            let b3 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res2 t1
            if b3
            then
              let fsig ← FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl (_root_.Sum.inr (s10,
                  is_signed_ty, checked, val, val1, l, res2, none,
                  none, none, none, some (core.result.Result.Ok t),
                  none, none, none, none, none, none, none, none,
                  none, none, none, none, none, none, none, none,
                  none, i, s1, s2, s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked res2 chk_t
                let r1 ←
                  core.option.Option.ok_or o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } : ParseIntErrorPublic)
                ok (_root_.Sum.inl (_root_.Sum.inr (s10,
                  is_signed_ty, checked, val, val1, l, res2, none,
                  none, none, none, some r1, none, none, none,
                  none, none, none, none, none, none, none, none,
                  none, none, none, none, none, none, i, s1, s2,
                  s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked res2 chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl (_root_.Sum.inr (s10,
                is_signed_ty, checked, val, val1, l, res2, none,
                none, none, none, some r1, none, none, none, none,
                none, none, none, none, none, none, none, none,
                none, none, none, none, none, i, s1, s2, s3, s4)))
        else
          let s11 ← FromStrRadixHelperInst.TREE
          let t1 ← Slice.index_usize s11 (Slice.len s10)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul t1 val3
          let res2 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub res1 t2
          ok (_root_.Sum.inr (s10, res2))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame ParseIntErrorPublic) residual
        ok (_root_.Sum.inl (_root_.Sum.inr (s6, is_signed_ty,
          checked, val, val1, l, res1, none, none, none, some r1,
          none, none, none, none, none, none, none, none, none,
          none, none, none, none, none, none, none, none, none, i,
          s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s6.val.length - 2 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s6.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u16
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_2_chars_spec s6 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 2) := by rw [← hs5]; rw [allDigits_take_two _ hN]; exact ⟨hr.1, hr.2.1⟩
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 2) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 2 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 2) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 2 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 2) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res1 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res1 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 2) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 2)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res1 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res1 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 2 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 2, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [← allDigits_take_two _ hN, hs5]
      exact allDigits_take (allDigits_drop hall k) 2
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 4-byte chunk at `s10`. -/
theorem negchunk4_s10_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s10 : Slice U8) (res2 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s10 res2) (hN : 4 ≤ s10.val.length) :
    (
      do
      let r ← parse_4_chars s10
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2
        =>
        let val3 ← FromStrRadixHelperInst.from_u16 val2
        let s14 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 4#usize } s10
        let b3 : Bool ← core.slice.Slice.is_empty s14
        if b3
        then
          let res3 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res2 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl (_root_.Sum.inr (s14,
              is_signed_ty, none, val, val1, l, res3,
              none, none, none, none, none, none, some
              (core.result.Result.Ok res3), none, none,
              none, none, none, none, none, none, none,
              none, none, none, none, none, none, i, s1,
              s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ← FromStrRadixHelperInst.TAIL
            let b4 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res3 t1
            if b4
            then
              let fsig ← FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                  is_signed_ty, checked, val, val1, l,
                  res3, none, none, none, none, none,
                  none, some (core.result.Result.Ok t),
                  none, none, none, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, i, s1, s2, s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked res3
                    chk_t
                let r1 ←
                  core.option.Option.ok_or o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } : ParseIntErrorPublic)
                ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                  is_signed_ty, checked, val, val1, l,
                  res3, none, none, none, none, none,
                  none, some r1, none, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, none, none, i, s1,
                  s2, s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked res3
                  chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                is_signed_ty, checked, val, val1, l,
                res3, none, none, none, none, none, none,
                some r1, none, none, none, none, none,
                none, none, none, none, none, none, none,
                none, none, none, i, s1, s2, s3, s4)))
        else
          let s15 ← FromStrRadixHelperInst.TREE
          let t1 ← Slice.index_usize s15 (Slice.len s14)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res3 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res2 t2
          ok (_root_.Sum.inr (s14, res3))
      | core.ops.control_flow.ControlFlow.Break residual
        =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame ParseIntErrorPublic)
            residual
        ok (_root_.Sum.inl (_root_.Sum.inr (s10,
          is_signed_ty, checked, val, val1, l, res2,
          none, none, none, none, none, some r1, none,
          none, none, none, none, none, none, none, none,
          none, none, none, none, none, none, none, i,
          s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s10.val.length - 4 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s10.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u16
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_4_chars_spec s10 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 4) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 4) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 4 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 4) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 4 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 4) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res2 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res2 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 4) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 4)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res2 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res2 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 4 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 4, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 4
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 8-byte chunk at `s14`. -/
theorem negchunk8_s14_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s14 : Slice U8) (res3 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s14 res3) (hN : 8 ≤ s14.val.length) :
    (
      do
      let r ← parse_8_chars s14
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch
          r
      match cf with
      |
        core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u32 val2
        let s18 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 8#usize } s14
        let b4 : Bool ←
          core.slice.Slice.is_empty s18
        if b4
        then
          let res4 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res3 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl (_root_.Sum.inr
              (s18, is_signed_ty, none, val,
              val1, l, res4, none, none, none,
              none, none, none, none, none,
              some (core.result.Result.Ok
              res4), none, none, none, none,
              none, none, none, none, none,
              none, none, none, none, i, s1,
              s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ←
              FromStrRadixHelperInst.TAIL
            let b5 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res4 t1
            if b5
            then
              let fsig ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl
                  (_root_.Sum.inr (s18,
                  is_signed_ty, checked, val,
                  val1, l, res4, none, none,
                  none, none, none, none, none,
                  none, some
                  (core.result.Result.Ok t),
                  none, none, none, none, none,
                  none, none, none, none, none,
                  none, none, none, i, s1, s2,
                  s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res4 chk_t
                let r1 ←
                  core.option.Option.ok_or o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } : ParseIntErrorPublic)
                ok (_root_.Sum.inl
                  (_root_.Sum.inr (s18,
                  is_signed_ty, checked, val,
                  val1, l, res4, none, none,
                  none, none, none, none, none,
                  none, some r1, none, none,
                  none, none, none, none, none,
                  none, none, none, none, none,
                  none, i, s1, s2, s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res4 chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl
                (_root_.Sum.inr (s18,
                is_signed_ty, checked, val,
                val1, l, res4, none, none,
                none, none, none, none, none,
                none, some r1, none, none,
                none, none, none, none, none,
                none, none, none, none, none,
                none, i, s1, s2, s3, s4)))
        else
          let s19 ←
            FromStrRadixHelperInst.TREE
          let t1 ← Slice.index_usize s19 (Slice.len s18)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res4 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res3 t2
          ok (_root_.Sum.inr (s18, res4))
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame
            ParseIntErrorPublic) residual
        ok (_root_.Sum.inl (_root_.Sum.inr
          (s14, is_signed_ty, checked, val,
          val1, l, res3, none, none, none,
          none, none, none, none, some r1,
          none, none, none, none, none, none,
          none, none, none, none, none, none,
          none, none, i, s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s14.val.length - 8 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s14.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u32
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_8_chars_spec s14 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 8) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 8) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 8 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 8) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 8 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 8) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res3 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res3 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 8) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 8)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res3 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res3 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 8 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 8, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 8
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 16-byte chunk at `s18`. -/
theorem negchunk16_s18_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s18 : Slice U8) (res4 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s18 res4) (hN : 16 ≤ s18.val.length) :
    (
      do
      let r ← parse_16_chars s18
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch
          r
      match cf with
      |
        core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u64
            val2
        let s22 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 16#usize } s18
        let b5 : Bool ←
          core.slice.Slice.is_empty
            s22
        if b5
        then
          let res5 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res4 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl
              (_root_.Sum.inr (s22,
              is_signed_ty, none,
              val, val1, l, res5,
              none, none, none, none,
              none, none, none, none,
              none, none, some
              (core.result.Result.Ok
              res5), none, none,
              none, none, none, none,
              none, none, none, none,
              none, i, s1, s2, s3,
              s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ←
              FromStrRadixHelperInst.TAIL
            let b6 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res5 t1
            if b6
            then
              let fsig ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s22, is_signed_ty,
                  checked, val, val1,
                  l, res5, none,
                  none, none, none,
                  none, none, none,
                  none, none, none,
                  some
                  (core.result.Result.Ok
                  t), none, none,
                  none, none, none,
                  none, none, none,
                  none, none, none,
                  i, s1, s2, s3,
                  s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res5 chk_t
                let r1 ←
                  core.option.Option.ok_or
                    o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } :
                    ParseIntErrorPublic)
                ok (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s22, is_signed_ty,
                  checked, val, val1,
                  l, res5, none,
                  none, none, none,
                  none, none, none,
                  none, none, none,
                  some r1, none,
                  none, none, none,
                  none, none, none,
                  none, none, none,
                  none, i, s1, s2,
                  s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res5 chk_t
              let r1 ←
                core.option.Option.ok_or
                  o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } :
                  ParseIntErrorPublic)
              ok (_root_.Sum.inl
                (_root_.Sum.inr (s22,
                is_signed_ty,
                checked, val, val1,
                l, res5, none, none,
                none, none, none,
                none, none, none,
                none, none, some r1,
                none, none, none,
                none, none, none,
                none, none, none,
                none, none, i, s1,
                s2, s3, s4)))
        else
          let s23 ←
            FromStrRadixHelperInst.TREE
          let t1 ←
            Slice.index_usize s23 (Slice.len s22)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res5 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res4 t2
          ok (_root_.Sum.inr (s22,
            res5))
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame
            ParseIntErrorPublic)
            residual
        ok (_root_.Sum.inl
          (_root_.Sum.inr (s18,
          is_signed_ty, checked, val,
          val1, l, res4, none, none,
          none, none, none, none,
          none, none, none, some r1,
          none, none, none, none,
          none, none, none, none,
          none, none, none, none, i,
          s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s18.val.length - 16 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s18.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u64
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_16_chars_spec s18 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 16) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 16) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 16 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 16) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 16 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 16) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res4 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res4 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 16) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 16)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res4 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res4 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 16 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 16, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 16
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 32-byte chunk at `s22`. -/
theorem negchunk32_s22_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s22 : Slice U8) (res5 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s22 res5) (hN : 32 ≤ s22.val.length) :
    (
      do
      let r ←
        parse_32_chars s22
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch
          r
      match cf with
      |
        core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u128
            val2
        let s25 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 32#usize } s22
        let b5 : Bool ←
          core.slice.Slice.is_empty
            s25
        if b5
        then
          let res6 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res5 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl
              (_root_.Sum.inr
              (s25,
              is_signed_ty,
              none, val, val1,
              l, res6, none,
              none, none, none,
              none, none, none,
              none, none, none,
              none, none, some
              (core.result.Result.Ok
              res6), none,
              none, none, none,
              none, none, none,
              none, none, i,
              s1, s2, s3, s4)))
          | some p =>
            let (chk, chk_t) :=
              p
            let t1 ←
              FromStrRadixHelperInst.TAIL
            let b6 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res6 t1
            if b6
            then
              let i7 ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = i7
              then
                ok
                  (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s25,
                  is_signed_ty,
                  checked, val,
                  val1, l,
                  res6, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, some
                  (core.result.Result.Ok
                  t), none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  i, s1, s2,
                  s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res6 chk_t
                let r1 ←
                  core.option.Option.ok_or
                    o1
                    (
                    {
                    kind :=
                    core.num.error.IntErrorKind.NegOverflow
                    } :
                    ParseIntErrorPublic)
                ok
                  (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s25,
                  is_signed_ty,
                  checked, val,
                  val1, l,
                  res6, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, some
                  r1, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  i, s1, s2,
                  s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res6 chk_t
              let r1 ←
                core.option.Option.ok_or
                  o1
                  ({
                    kind :=
                    core.num.error.IntErrorKind.NegOverflow
                   } :
                  ParseIntErrorPublic)
              ok
                (_root_.Sum.inl
                (_root_.Sum.inr
                (s25,
                is_signed_ty,
                checked, val,
                val1, l, res6,
                none, none,
                none, none,
                none, none,
                none, none,
                none, none,
                none, none,
                some r1, none,
                none, none,
                none, none,
                none, none,
                none, none, i,
                s1, s2, s3,
                s4)))
        else
          let s26 ←
            FromStrRadixHelperInst.TREE
          let i7 :=
            Slice.len s25
          let t1 ←
            Slice.index_usize
              s26 i7
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res6 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res5 t2
          ok (_root_.Sum.inr
            (s25, res6))
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T
            (core.convert.FromSame
            ParseIntErrorPublic)
            residual
        ok (_root_.Sum.inl
          (_root_.Sum.inr (s22,
          is_signed_ty,
          checked, val, val1,
          l, res5, none, none,
          none, none, none,
          none, none, none,
          none, none, none,
          some r1, none, none,
          none, none, none,
          none, none, none,
          none, none, i, s1,
          s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s22.val.length - 32 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s22.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u128
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_32_chars_spec s22 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 32) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 32) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 32 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 32) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 32 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 32) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res5 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res5 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 32) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 32)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res5 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res5 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 32 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 32, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 32
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 16-byte chunk at `s24`. -/
theorem negchunk16_s24_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s24 : Slice U8) (res6 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s24 res6) (hN : 16 ≤ s24.val.length) :
    (
      do
      let r ←
        parse_16_chars s24
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch
          r
      match cf with
      |
        core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u64
            val2
        let s26 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 16#usize } s24
        let b5 : Bool ←
          core.slice.Slice.is_empty
            s26
        if b5
        then
          let res7 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res6 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl
              (_root_.Sum.inr
              (s26, is_signed_ty,
              none, val, val1, l,
              res7, none, none,
              none, none, none,
              none, none, none,
              none, none, none,
              none, none, none,
              some
              (core.result.Result.Ok
              res7), none, none,
              none, none, none,
              none, none, i, s1,
              s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ←
              FromStrRadixHelperInst.TAIL
            let b6 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res7 t1
            if b6
            then
              let fsig ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok
                  (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s26,
                  is_signed_ty,
                  checked, val,
                  val1, l, res7,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  some
                  (core.result.Result.Ok
                  t), none, none,
                  none, none,
                  none, none,
                  none, i, s1,
                  s2, s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res7 chk_t
                let r1 ←
                  core.option.Option.ok_or
                    o1
                    ({
                      kind :=
                      core.num.error.IntErrorKind.NegOverflow
                     } :
                    ParseIntErrorPublic)
                ok
                  (_root_.Sum.inl
                  (_root_.Sum.inr
                  (s26,
                  is_signed_ty,
                  checked, val,
                  val1, l, res7,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  none, none,
                  some r1, none,
                  none, none,
                  none, none,
                  none, none, i,
                  s1, s2, s3,
                  s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res7 chk_t
              let r1 ←
                core.option.Option.ok_or
                  o1
                  ({
                     kind :=
                      core.num.error.IntErrorKind.NegOverflow
                   } :
                  ParseIntErrorPublic)
              ok (_root_.Sum.inl
                (_root_.Sum.inr
                (s26,
                is_signed_ty,
                checked, val,
                val1, l, res7,
                none, none, none,
                none, none, none,
                none, none, none,
                none, none, none,
                none, none, some
                r1, none, none,
                none, none, none,
                none, none, i,
                s1, s2, s3, s4)))
        else
          let s27 ←
            FromStrRadixHelperInst.TREE
          let t1 ←
            Slice.index_usize s27
              (Slice.len s26)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res7 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res6 t2
          ok (_root_.Sum.inr
            (s26, res7))
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T
            (core.convert.FromSame
            ParseIntErrorPublic)
            residual
        ok (_root_.Sum.inl
          (_root_.Sum.inr (s24,
          is_signed_ty, checked,
          val, val1, l, res6,
          none, none, none, none,
          none, none, none, none,
          none, none, none, none,
          none, some r1, none,
          none, none, none, none,
          none, none, none, i,
          s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s24.val.length - 16 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s24.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u64
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_16_chars_spec s24 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 16) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 16) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 16 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 16) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 16 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 16) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res6 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res6 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 16) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 16)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res6 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res6 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 16 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 16, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 16
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 8-byte chunk at `s20`. -/
theorem negchunk8_s20_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s20 : Slice U8) (res5 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s20 res5) (hN : 8 ≤ s20.val.length) :
    (
      do
      let r ← parse_8_chars s20
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch
          r
      match cf with
      |
        core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u32
            val2
        let s22 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 8#usize } s20
        let b4 : Bool ←
          core.slice.Slice.is_empty s22
        if b4
        then
          let res6 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res5 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl
              (_root_.Sum.inr (s22,
              is_signed_ty, none, val,
              val1, l, res6, none, none,
              none, none, none, none, none,
              none, none, none, none, none,
              none, none, none, none, some
              (core.result.Result.Ok res6),
              none, none, none, none, none,
              i, s1, s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ←
              FromStrRadixHelperInst.TAIL
            let b5 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res6 t1
            if b5
            then
              let fsig ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl
                  (_root_.Sum.inr (s22,
                  is_signed_ty, checked,
                  val, val1, l, res6, none,
                  none, none, none, none,
                  none, none, none, none,
                  none, none, none, none,
                  none, none, none, some
                  (core.result.Result.Ok
                  t), none, none, none,
                  none, none, i, s1, s2,
                  s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res6 chk_t
                let r1 ←
                  core.option.Option.ok_or
                    o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } :
                    ParseIntErrorPublic)
                ok (_root_.Sum.inl
                  (_root_.Sum.inr (s22,
                  is_signed_ty, checked,
                  val, val1, l, res6, none,
                  none, none, none, none,
                  none, none, none, none,
                  none, none, none, none,
                  none, none, none, some
                  r1, none, none, none,
                  none, none, i, s1, s2,
                  s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res6 chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl
                (_root_.Sum.inr (s22,
                is_signed_ty, checked, val,
                val1, l, res6, none, none,
                none, none, none, none,
                none, none, none, none,
                none, none, none, none,
                none, none, some r1, none,
                none, none, none, none, i,
                s1, s2, s3, s4)))
        else
          let s23 ←
            FromStrRadixHelperInst.TREE
          let t1 ←
            Slice.index_usize s23 (Slice.len s22)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res6 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res5 t2
          ok (_root_.Sum.inr (s22, res6))
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame
            ParseIntErrorPublic) residual
        ok (_root_.Sum.inl (_root_.Sum.inr
          (s20, is_signed_ty, checked, val,
          val1, l, res5, none, none, none,
          none, none, none, none, none,
          none, none, none, none, none,
          none, none, some r1, none, none,
          none, none, none, none, i, s1,
          s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s20.val.length - 8 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s20.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u32
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_8_chars_spec s20 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 8) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 8) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 8 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 8) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 8 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 8) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res5 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res5 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 8) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 8)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res5 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res5 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 8 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 8, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 8
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 4-byte chunk at `s16`. -/
theorem negchunk4_s16_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s16 : Slice U8) (res4 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s16 res4) (hN : 4 ≤ s16.val.length) :
    (
      do
      let r ← parse_4_chars s16
      let cf ←
        core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue
        val2 =>
        let val3 ←
          FromStrRadixHelperInst.from_u16 val2
        let s18 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 4#usize } s16
        let b3 : Bool ←
          core.slice.Slice.is_empty s18
        if b3
        then
          let res5 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res4 val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl (_root_.Sum.inr (s18,
              is_signed_ty, none, val, val1, l, res5,
              none, none, none, none, none, none,
              none, none, none, none, none, none,
              none, none, none, none, none, none,
              some (core.result.Result.Ok res5),
              none, none, none, i, s1, s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ← FromStrRadixHelperInst.TAIL
            let b4 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res5 t1
            if b4
            then
              let fsig ←
                FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl (_root_.Sum.inr
                  (s18, is_signed_ty, checked, val,
                  val1, l, res5, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, some
                  (core.result.Result.Ok t), none,
                  none, none, i, s1, s2, s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked
                    res5 chk_t
                let r1 ←
                  core.option.Option.ok_or o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } : ParseIntErrorPublic)
                ok (_root_.Sum.inl (_root_.Sum.inr
                  (s18, is_signed_ty, checked, val,
                  val1, l, res5, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, none, none, none,
                  none, none, none, some r1, none,
                  none, none, i, s1, s2, s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked
                  res5 chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl (_root_.Sum.inr
                (s18, is_signed_ty, checked, val,
                val1, l, res5, none, none, none,
                none, none, none, none, none, none,
                none, none, none, none, none, none,
                none, none, none, some r1, none,
                none, none, i, s1, s2, s3, s4)))
        else
          let s19 ← FromStrRadixHelperInst.TREE
          let t1 ← Slice.index_usize s19 (Slice.len s18)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul
              t1 val3
          let res5 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub
              res4 t2
          ok (_root_.Sum.inr (s18, res5))
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame
            ParseIntErrorPublic) residual
        ok (_root_.Sum.inl (_root_.Sum.inr (s16,
          is_signed_ty, checked, val, val1, l, res4,
          none, none, none, none, none, none, none,
          none, none, none, none, none, none, none,
          none, none, none, some r1, none, none,
          none, none, i, s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s16.val.length - 4 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s16.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u16
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_4_chars_spec s16 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 4) := by rw [← hs5]; exact hr.1
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 4) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 4 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 4) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 4 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 4) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res4 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res4 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 4) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 4)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res4 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res4 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 4 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 4, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [hs5]
      exact allDigits_take (allDigits_drop hall k) 4
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

/-- The 2-byte chunk at `s12`. -/
theorem negchunk2_s12_spec {T : Type} {FromStrRadixHelperInst : parse.FromStrRadixHelper T}
    {toInt : T → ℤ} {lo hi : ℤ} {c : ℕ} (hF : Faithful FromStrRadixHelperInst toInt lo hi c)
    (hlo : lo < 0) {D0 D : List U8} {checked : Option (U8 × T)}
    (hH : NegHandover toInt lo hi c D0 D checked) (t : T) (ht : toInt t = lo)
    (s12 : Slice U8) (res3 : T) (is_signed_ty : Bool) (val val1 : U8) (l : Usize) (i : U8)
    (s1 s2 s3 s4 : Slice U8) (hinv : NegBlockInv toInt D s12 res3) (hN : 2 ≤ s12.val.length) :
    (
      do
      let r ← parse_2_chars s12
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let val3 ← FromStrRadixHelperInst.from_u16 val2
        let s14 ←
          core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := 2#usize } s12
        let b2 : Bool ← core.slice.Slice.is_empty s14
        if b2
        then
          let res4 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub res3
              val3
          match (generalizing := false) checked with
          | none =>
            ok (_root_.Sum.inl (_root_.Sum.inr (s14,
              is_signed_ty, none, val, val1, l, res4, none,
              none, none, none, none, none, none, none, none,
              none, none, none, none, none, none, none, none,
              none, none, none, some (core.result.Result.Ok
              res4), none, i, s1, s2, s3, s4)))
          | some p =>
            let (chk, chk_t) := p
            let t1 ← FromStrRadixHelperInst.TAIL
            let b3 : Bool ←
              FromStrRadixHelperInst.corecmpPartialOrdInst.partialEqInst.eq
                res4 t1
            if b3
            then
              let fsig ← FromStrRadixHelperInst.FIRST_SIG
              if chk = fsig
              then
                ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                  is_signed_ty, checked, val, val1, l, res4,
                  none, none, none, none, none, none, none,
                  none, none, none, none, none, none, none,
                  none, none, none, none, none, none, some
                  (core.result.Result.Ok t), none, i, s1, s2,
                  s3, s4)))
              else
                let o1 ←
                  FromStrRadixHelperInst.sub_checked res4 chk_t
                let r1 ←
                  core.option.Option.ok_or o1
                    ({
                       kind :=
                         core.num.error.IntErrorKind.NegOverflow
                     } : ParseIntErrorPublic)
                ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                  is_signed_ty, checked, val, val1, l, res4,
                  none, none, none, none, none, none, none,
                  none, none, none, none, none, none, none,
                  none, none, none, none, none, none, some r1,
                  none, i, s1, s2, s3, s4)))
            else
              let o1 ←
                FromStrRadixHelperInst.sub_checked res4 chk_t
              let r1 ←
                core.option.Option.ok_or o1
                  ({
                     kind :=
                       core.num.error.IntErrorKind.NegOverflow
                   } : ParseIntErrorPublic)
              ok (_root_.Sum.inl (_root_.Sum.inr (s14,
                is_signed_ty, checked, val, val1, l, res4,
                none, none, none, none, none, none, none, none,
                none, none, none, none, none, none, none, none,
                none, none, none, none, some r1, none, i, s1,
                s2, s3, s4)))
        else
          let s15 ← FromStrRadixHelperInst.TREE
          let t1 ← Slice.index_usize s15 (Slice.len s14)
          let t2 ←
            FromStrRadixHelperInst.coreopsarithMulInst.mul t1
              val3
          let res4 ←
            FromStrRadixHelperInst.coreopsarithSubInst.sub res3
              t2
          ok (_root_.Sum.inr (s14, res4))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            T (core.convert.FromSame ParseIntErrorPublic)
            residual
        ok (_root_.Sum.inl (_root_.Sum.inr (s12, is_signed_ty,
          checked, val, val1, l, res3, none, none, none, none,
          none, none, none, none, none, none, none, none, none,
          none, none, none, none, none, none, some r1, none,
          none, i, s1, s2, s3, s4))) : Result (_root_.Sum (_root_.Sum ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (core.ops.range.Range Std.I32) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8)) ((Slice Std.U8) × Bool × (Option (Std.U8 × T)) × Std.U8 × Std.U8 × Std.Usize × T × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × (Option (core.result.Result T ParseIntErrorPublic)) × Std.U8 × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8))) ((Slice Std.U8) × T)))
      ⦃ NegBlockPost toInt lo hi D0 D (s12.val.length - 2 + 1) ⦄ := by
  obtain ⟨k, hk, hs5, hallk, hres1⟩ := hinv
  have hlen5 : s12.val.length = D.length - k := by rw [hs5]; simp
  have hDlt := hH.len_lt
  have hSub := hF.sub
  have hMul := hF.mul
  have hTR := hF.TREE
  have hFW := hF.from_u16
  have hSC := hF.sub_checked
  have hEq := hF.eq
  have hTL := hF.TAIL
  have hFS := hF.FIRST_SIG
  step with parse_2_chars_spec s12 hN as ⟨r, hr⟩
  step as ⟨cf, hcf⟩
  rcases r with v | e
  · -- all digits
    simp only at hr hcf
    subst hcf
    have hNd : allDigits ((D.drop k).take 2) := by rw [← hs5]; rw [allDigits_take_two _ hN]; exact ⟨hr.1, hr.2.1⟩
    have hv : (v.val : ℤ) = (decimal ((D.drop k).take 2) : ℤ) := by rw [← hs5]; exact_mod_cast hr.2.2
    obtain ⟨hall', hv0, hvhi, hmr, har, hresnew, hfull⟩ :=
      chunk_step_neg hF hlo D hDlt k 2 (by omega) hallk hNd (v.val : ℤ) hv
    step as ⟨val3, hval3⟩
    have hval3' : toInt val3 = (v.val : ℤ) := hval3 hvhi
    step as ⟨s9, hs9, hs9len⟩
    have hs9' : (↑s9 : List U8) = D.drop (k + 2) := by rw [hs9, hs5, drop_drop_val]
    step as ⟨b2, hb2⟩
    split
    · -- the chunk ends the bytes
      rename_i hb2t
      have hempty : k + 2 = D.length := by
        have h9z : (↑s9 : List U8) = [] := by
          have h := hb2; rw [hb2t] at h; simp [Slice.length] at h; exact h
        rw [hs9', List.drop_eq_nil_iff] at h9z; omega
      have h0 : D.length - (k + 2) = 0 := by omega
      rw [h0, pow_zero, one_mul] at har
      have hsub : InRange lo hi (toInt res3 - toInt val3) := by rw [hres1, hval3']; exact har
      step with hSub res3 val3 hsub as ⟨res2, hres2⟩
      have hres2' : toInt res2 = -(decimal D : ℤ) := by rw [hres2, hres1, hval3']; exact hfull hempty
      have hallD : allDigits D := by have := hall'; rwa [hempty, List.take_length] at this
      revert hH
      rcases hck : checked with _ | ⟨d, ct⟩ <;> intro hH <;> dsimp only
      · rw [WP.spec_ok]
        exact SlotsOK_of_mem (by simp) (final_neg_unchecked hF hlo hH hallD res2 hres2') (by simp)
      · step as ⟨tl, htl⟩
        step as ⟨b3, hb3⟩
        split
        · rename_i hb3t
          have heq : toInt res2 = toInt tl := by
            have h := hb3; rw [hb3t] at h; simpa using h.symm
          step as ⟨fs, hfs⟩
          split
          · rename_i hdfs
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp)
              (final_neg_tail hF hH hallD res2 hres2' tl t (htl hlo) ht heq (by rw [hdfs]; exact hfs)) (by simp)
          · step as ⟨o1, ho1⟩
            apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
            intro r1 hr1
            rw [WP.spec_ok]
            exact SlotsOK_of_mem (by simp) hr1 (by simp)
        · step as ⟨o1, ho1⟩
          apply WP.spec_bind (final_neg_checked hF hH hallD res2 hres2' o1 ho1)
          intro r1 hr1
          rw [WP.spec_ok]
          exact SlotsOK_of_mem (by simp) hr1 (by simp)
    · -- more bytes follow: scale and subtract
      step as ⟨tr, htrlen, htr⟩
      have hs9l : s9.len.val = D.length - (k + 2) := by rw [Slice.len_val]; simp [Slice.length, hs9']
      step with Slice.index_usize_spec tr s9.len
        (by rw [hs9l]; simp only [Slice.length]; rw [htrlen]; omega) as ⟨tt, htt⟩
      have htv : toInt tt = 10 ^ (D.length - (k + 2)) := by
        rw [htt]; simp only [hs9l]; exact htr _ (by omega)
      have hmr' : InRange lo hi (toInt tt * toInt val3) := by rw [htv, hval3']; exact hmr
      step with hMul tt val3 hmr' as ⟨t2, ht2⟩
      have hsub' : InRange lo hi (toInt res3 - toInt t2) := by rw [ht2, htv, hval3', hres1]; exact har
      step with hSub res3 t2 hsub' as ⟨res2, hres2⟩
      have hb2f : ¬ b2 = true := by assumption
      have hkN : k + 2 < D.length := by
        have h0 : ¬ (↑s9 : List U8).length = 0 := by
          intro h0; apply hb2f; rw [hb2]; simp [Slice.length, h0]
        rw [hs9', List.length_drop] at h0; omega
      refine ⟨⟨k + 2, hkN, hs9', hall', by rw [hres2, ht2, htv, hval3', hres1]; exact hresnew⟩, ?_⟩
      rw [hs9', List.length_drop, hlen5]; omega
  · -- a non-digit in the chunk
    simp only at hr hcf
    subst hcf
    obtain ⟨hnd, hkind⟩ := hr
    have hnot : ¬ allDigits D := by
      intro hall
      apply hnd
      rw [← allDigits_take_two _ hN, hs5]
      exact allDigits_take (allDigits_drop hall k) 2
    step as ⟨r1, hr1⟩
    subst hr1
    exact SlotsOK_of_mem (by simp) (final_neg_invalid hF hH hnot e hkind) (by simp)

end atoi_radix10
