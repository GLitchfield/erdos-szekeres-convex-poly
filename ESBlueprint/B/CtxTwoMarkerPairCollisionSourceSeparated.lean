import ESBlueprint.B.CtxBinaryCapacityPairIntersectionSourceWitnesses
import ESBlueprint.B.CtxMixedCapacityChildrenSeparatedByOlderMarkerGlobalFive

set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Under the exact two-marker chosen history at chosen global at most five, every ordered pair shared by the canonical low/high active pair unions has explicit source-active low/high capacity witnesses that straddle the older marker. Both pair coordinates remain in both original-history opposite-rank intervals, turning a collision into simultaneous positional and rank geometry.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_binary_capacity_pair_intersection_source_witnesses, ErdosSzekeres.ctx_mixed_capacity_children_separated_by_older_marker_global_five
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_pair_collision_source_separated (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) : let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun q => match σ.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); let sourceInterval : ℕ → Finset ℕ := fun q => Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q); ∀ z ∈ (pairs 0) ∩ (pairs 1), ∃ low high, low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧ 0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧ high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧ 0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧ z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧ z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high ∧ ((x < y ∧ low < y ∧ y < high) ∨ (y < x ∧ high < y ∧ y < low)) := by
  classical
  cases s with
  | lower =>
    dsimp only
    intro z hz
    obtain ⟨low, high, hlowMem, hlowCup, hlowCap, hlowCapacity,
      hhighMem, hhighCup, hhighCap, hhighCapacity, hzOrdered,
      hzLowLeft, hzLowRight, hzHighLeft, hzHighRight⟩ :=
        ctx_binary_capacity_pair_intersection_source_witnesses
          σ hpositive Ctx.Side.lower t z hz
    have hseparated := ctx_mixed_capacity_children_separated_by_older_marker_global_five
      σ Ctx.Side.lower N M x y high low hN hM hNM hNs hMs hx hy hglobal hchosen
        hhighMem hlowMem hhighCapacity hlowCapacity
    exact ⟨low, high, hlowMem, hlowCup, hlowCap, hlowCapacity,
      hhighMem, hhighCup, hhighCap, hhighCapacity, hzOrdered,
      hzLowLeft, hzLowRight, hzHighLeft, hzHighRight, hseparated⟩
  | upper =>
    dsimp only
    intro z hz
    obtain ⟨low, high, hlowMem, hlowCup, hlowCap, hlowCapacity,
      hhighMem, hhighCup, hhighCap, hhighCapacity, hzOrdered,
      hzLowLeft, hzLowRight, hzHighLeft, hzHighRight⟩ :=
        ctx_binary_capacity_pair_intersection_source_witnesses
          σ hpositive Ctx.Side.upper t z hz
    have hseparated := ctx_mixed_capacity_children_separated_by_older_marker_global_five
      σ Ctx.Side.upper N M x y high low hN hM hNM hNs hMs hx hy hglobal hchosen
        hhighMem hlowMem hhighCapacity hlowCapacity
    exact ⟨low, high, hlowMem, hlowCup, hlowCap, hlowCapacity,
      hhighMem, hhighCup, hhighCap, hhighCapacity, hzOrdered,
      hzLowLeft, hzLowRight, hzHighLeft, hzHighRight, hseparated⟩

end ErdosSzekeres
