import ESBlueprint.B.CtxOneLevelRootOutsidePairLeafThresholdAgreement
import ESBlueprint.B.CtxInsidePairLeafThresholdMonoOfTwoRuns
import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxBoundAttainedByEndCut

set_option maxHeartbeats 6000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For an arbitrary well-formed two-run context, contraction of adjacent child copies weakly increases the full singleton-cut value at the mapped child while keeping the same side and coupling, when the axis opposite the source cut is at most two. The actual fresh marker at the omitted source child annihilates the complementary source bound; combine closed inside and outside leaf comparisons. Arbitrary indexed histories and both source orientations; no one-level root or old maximum restriction. This is a source-cut region, distinct from restricting the old-marker opposite axis, and does not settle the remaining positive-source side-changing axis-two exchange.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_one_level_root_outside_pair_leaf_threshold_agreement, ErdosSzekeres.ctx_inside_pair_leaf_threshold_mono_of_two_runs, ErdosSzekeres.ctx_bound_le_sum_point_bases
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_pair_contraction_singleton_value_mono_of_opposite_global_two (σ : Ctx.Context) (hwf : σ.WellFormed) (left right : List Ctx.Letter) (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) (hruns : 2 ≤ σ.numRuns) (p : ℕ) (hp : p ∈ σ.childPositions) (s : Ctx.Side) (c : ℕ) (hc : 1 ≤ c) (hck : c ≤ σ.k - 2) (hsmall : (match s with | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u) ≤ 2) : let ρ : Ctx.Context := { σ with word := left ++ [Ctx.Letter.child] ++ right }; let q := if p ≤ left.length then p else p - 1; decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) σ.k + (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower) (σ.k - 1 - c)).bound ≤ decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1) ((ρ.part [q] s c).cupLimit q q + 1) σ.k + (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower) (σ.k - 1 - c)).bound := by
  classical
  let ρ : Context := { σ with word := left ++ [Letter.child] ++ right }
  let q := if p ≤ left.length then p else p - 1
  let rest := σ.childPositions.filter (fun r => r ≠ p)
  let opposite := match s with | Side.lower => Side.upper | Side.upper => Side.lower
  let τ := σ.part rest opposite (σ.k - 1 - c)
  have hpositive : ∀ x j v, σ.letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
    exact (hwf.2.2.2.2.2 x j v hx).1
  have hMarkerZero (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ)
      (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
      (hglobal : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 2) :
      (∀ fuel : ℕ, boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
    have hPoint : ∀ p ∈ σ.childPositions,
        baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
      intro p hp
      have hpx : p ≠ x := by
        intro he
        subst x
        have hc := of_decide_eq_true (List.mem_filter.mp hp).2
        have he := (List.mem_filter.mp hx).2
        simp [hc] at he
      have hChain : 1 ≤ σ.chainExt s p p := by
        by_cases h : p < x
        · have hright := hOneRight σ s N p x hNOn hx h
          unfold chainExt
          omega
        · have hleft := hOneLeft σ s N p x hNOn hx (by omega)
          unfold chainExt
          omega
      cases s with
      | lower =>
        dsimp only at hglobal
        have hzero : σ.cupLimit p p = 0 := by
          simp only [cupLimit]
          omega
        simp [baseOf,hzero]
      | upper =>
        dsimp only at hglobal
        have hzero : σ.capLimit p p = 0 := by
          simp only [capLimit]
          omega
        simp [baseOf,hzero]
    have hMap :
        σ.childPositions.map (fun p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k) =
          σ.childPositions.map (fun _ => 0) := by
      apply List.map_congr_left
      intro p hp
      exact hPoint p hp
    have hBound : σ.bound = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hMap,List.sum_map_zero] using ctx_bound_le_sum_point_bases σ
    have hFuel (fuel : ℕ) : boundFuel fuel σ = 0 := by
      have hle : boundFuel fuel σ ≤ σ.bound := by
        by_cases hf : σ.childPositions.length+1 ≤ fuel
        · exact (boundFuel_eq_bound σ hf).le
        · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
      rw [hBound] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact ⟨hFuel,hBound⟩
  have hpData : p < σ.word.length ∧ σ.letterAt p = Letter.child := by
    simpa only [childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq] using hp
  have he : τ.letterAt p = Letter.ext 1 opposite := by
    change (σ.part rest opposite (σ.k - 1 - c)).letterAt p = Letter.ext 1 opposite
    rw [part_letterAt_of_child σ rest opposite (σ.k - 1 - c) hpData.1 hpData.2]
    simp [rest]
  have hx : p ∈ τ.extPositions 1 := by
    change p ∈ (σ.part rest opposite (σ.k - 1 - c)).extPositions 1
    simp only [extPositions, List.mem_filter, List.mem_range, part_word_length]
    refine ⟨hpData.1, ?_⟩
    have hh : (σ.part rest opposite (σ.k - 1 - c)).letterAt p = Letter.ext 1 opposite := he
    simp [hh]
  have hSide : τ.sideAt 1 = opposite :=
    part_sideAt_one_of_mem hpositive rest opposite (σ.k - 1 - c) (q := p) hx
  have hN : 1 ∈ τ.levels := by
    change 1 ∈ (σ.part rest opposite (σ.k - 1 - c)).levels
    simp only [levels, List.mem_map, List.mem_range, part_maxima, List.length_cons]
    exact ⟨0, by omega, rfl⟩
  have hSmall : (match opposite with | Side.lower => τ.u | Side.upper => τ.a) ≤ 2 := by
    cases s <;> simpa [opposite, τ, part] using hsmall
  have hZero : τ.bound = 0 := by
    apply (hMarkerZero τ opposite 1 p hN hSide hx ?_).2
    cases s <;> simpa only [opposite, τ, part] using hsmall
  have hLeaf :
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
        ((σ.part [p] s c).cupLimit p p + 1) σ.k ≤
      decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
        ((ρ.part [q] s c).cupLimit q q + 1) σ.k := by
    by_cases hin : p = left.length ∨ p = left.length + 1
    · have hq : q = left.length := by
        dsimp only [q]
        split_ifs <;> rcases hin with h | h <;> omega
      simpa only [ρ, hq] using
        ctx_inside_pair_leaf_threshold_mono_of_two_runs σ hwf left right hword hruns p hp hin s c hc hck
    · have hp0 : p ≠ left.length := fun h => hin (Or.inl h)
      have hp1 : p ≠ left.length + 1 := fun h => hin (Or.inr h)
      simpa only [ρ, q] using
        (ctx_one_level_root_outside_pair_leaf_threshold_agreement σ hwf left right hword p hp hp0 hp1 s c hc hck).le
  have hTotal : decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) σ.k + τ.bound ≤
    decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
      ((ρ.part [q] s c).cupLimit q q + 1) σ.k +
      (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) opposite (σ.k - 1 - c)).bound := by
    rw [hZero, Nat.add_zero]
    exact hLeaf.trans (Nat.le_add_right _ _)
  cases s <;> simpa only [ρ, q, τ, rest, opposite] using hTotal


end ErdosSzekeres
