import ESBlueprint.B.CtxTwoMarkerPairCollisionSourceSeparated
import ESBlueprint.B.CtxTwoStraddlingPairCollisionsCommonWitnessIntervals
import ESBlueprint.B.RankPairTriangleIntersectionCardGeThreeOfTwoCommonRanks

set_option maxHeartbeats 12000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- In an exact two-marker chosen-global-five context, two distinct ordered pairs in the canonical low/high capacity-pruning pair intersection force that intersection to contain at least three pairs. Marker separation and interval monotonicity create two common ranks; their diagonals and sorted cross-pair lift back through exact pruning transport.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_pair_collision_source_separated, ErdosSzekeres.CtxTwoStraddlingPairCollisionsCommonWitnessIntervals, ErdosSzekeres.rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_two_pair_collision_intersection_three (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) : let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun q => match σ.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); ∀ z ∈ (pairs 0) ∩ (pairs 1), ∀ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w → 3 ≤ ((pairs 0) ∩ (pairs 1)).card := by
  classical
  dsimp only
  let capacity : ℕ → ℕ := fun q => match (generalizing := false) s with
    | Ctx.Side.lower => σ.cupLimit q q
    | Ctx.Side.upper => σ.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c =>
    σ.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with
    word := (List.range σ.word.length).map (fun q => match σ.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global : ℕ := match t with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c =>
    (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q =>
    Finset.Icc ((group c).leftExt t 0 q + 1)
      (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun q =>
      (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)))
  let sourceInterval : ℕ → Finset ℕ := fun q =>
    Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q)
  have hChild (c q : ℕ) : q ∈ (group c).childPositions ↔
      q ∈ σ.childPositions ∧ color q = c := by
    have hh : (group c).childPositions =
        σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive
        (support c) Ctx.Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hLimits (c p q : ℕ) :
      (group c).cupLimit p q = σ.cupLimit p q ∧
        (group c).capLimit p q = σ.capLimit p q :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.2.1 p q
  have hPure (c : ℕ) (v : Ctx.Side) (top q : ℕ) :
      (group c).leftExt v top q = σ.leftExt v top q ∧
        (group c).rightExt v top q = σ.rightExt v top q :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.1 v top q
  have hActive (c q : ℕ) : q ∈ active c ↔
      q ∈ σ.childPositions ∧ 0 < σ.cupLimit q q ∧
        0 < σ.capLimit q q ∧ color q = c := by
    simp only [active, Finset.mem_filter, List.mem_toFinset, hChild,
      (hLimits c q q).1, (hLimits c q q).2]
    tauto
  have hInterval (c q : ℕ) : interval c q = sourceInterval q := by
    simp only [interval, sourceInterval, (hPure c t 0 q).1, (hPure c t 0 q).2]
  have hGeometry := ctx_two_marker_pair_collision_source_separated
    σ hpositive s t N M x y hN hM hNM hNs hMs hx hy hglobal hchosen
  have hGeometry' : ∀ z ∈ (pairs 0) ∩ (pairs 1), ∃ low high,
      low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧
        0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧
      high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧
        0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧
      z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧
        z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high ∧
        ((x < y ∧ low < y ∧ y < high) ∨
          (y < x ∧ high < y ∧ y < low)) := by
    simpa only [capacity, color, support, group, global, active, interval,
      pairs, sourceInterval] using hGeometry
  suffices hResult : ∀ z ∈ (pairs 0) ∩ (pairs 1),
      ∀ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w →
        3 ≤ ((pairs 0) ∩ (pairs 1)).card by
    simpa only [capacity, color, support, group, global, active, interval,
      pairs] using hResult
  intro z hz w hw hzw
  obtain ⟨lowZ, highZ, hlowZMem, hlowZCup, hlowZCap, hlowZCapacity,
    hhighZMem, hhighZCup, hhighZCap, hhighZCapacity, _,
    hz1Low, hz2Low, hz1High, hz2High, hsepZ⟩ := hGeometry' z hz
  obtain ⟨lowW, highW, hlowWMem, hlowWCup, hlowWCap, hlowWCapacity,
    hhighWMem, hhighWCup, hhighWCap, hhighWCapacity, _,
    hw1Low, hw2Low, hw1High, hw2High, hsepW⟩ := hGeometry' w hw
  have hsep :
      (lowZ < y ∧ y < highZ ∧ lowW < y ∧ y < highW) ∨
        (highZ < y ∧ y < lowZ ∧ highW < y ∧ y < lowW) := by
    rcases hsepZ with ⟨hxy, hlZ, hZh⟩ | ⟨hyx, hhZ, hZl⟩
    · rcases hsepW with ⟨_, hlW, hWh⟩ | ⟨hyx', _, _⟩
      · exact Or.inl ⟨hlZ, hZh, hlW, hWh⟩
      · omega
    · rcases hsepW with ⟨hxy, _, _⟩ | ⟨_, hhW, hWl⟩
      · omega
      · exact Or.inr ⟨hhZ, hZl, hhW, hWl⟩
  obtain ⟨low, high, hlowChoice, hhighChoice, _,
    hz1Low', hz2Low', hz1High', hz2High',
    hw1Low', hw2Low', hw1High', hw2High',
    r, r', hrr', hrLow, hrHigh, hr'Low, hr'High⟩ :=
      CtxTwoStraddlingPairCollisionsCommonWitnessIntervals
        σ t global y z w lowZ highZ lowW highW hzw
          hz1Low hz2Low hz1High hz2High
          hw1Low hw2Low hw1High hw2High hsep
  have hlowData : low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧
      0 < σ.capLimit low low ∧ capacity low ≤ 2 := by
    rcases hlowChoice with rfl | rfl
    · exact ⟨hlowZMem, hlowZCup, hlowZCap, hlowZCapacity⟩
    · exact ⟨hlowWMem, hlowWCup, hlowWCap, hlowWCapacity⟩
  have hhighData : high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧
      0 < σ.capLimit high high ∧ 3 ≤ capacity high := by
    rcases hhighChoice with rfl | rfl
    · exact ⟨hhighZMem, hhighZCup, hhighZCap, hhighZCapacity⟩
    · exact ⟨hhighWMem, hhighWCup, hhighWCap, hhighWCapacity⟩
  have hlowColor : color low = 0 := by
    simp [color, hlowData.2.2.2]
  have hhighColor : color high = 1 := by
    have hnle : ¬ capacity high ≤ 2 := by omega
    simp [color, hnle]
  have hlowActive : low ∈ active 0 :=
    (hActive 0 low).mpr ⟨hlowData.1, hlowData.2.1,
      hlowData.2.2.1, hlowColor⟩
  have hhighActive : high ∈ active 1 :=
    (hActive 1 high).mpr ⟨hhighData.1, hhighData.2.1,
      hhighData.2.2.1, hhighColor⟩
  have hrLow' : r ∈ interval 0 low := by
    rw [hInterval 0 low]
    exact hrLow
  have hrHigh' : r ∈ interval 1 high := by
    rw [hInterval 1 high]
    exact hrHigh
  have hr'Low' : r' ∈ interval 0 low := by
    rw [hInterval 0 low]
    exact hr'Low
  have hr'High' : r' ∈ interval 1 high := by
    rw [hInterval 1 high]
    exact hr'High
  have hLocal := rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks
    (interval 0 low) (interval 1 high) r r' hrr'
      hrLow' hr'Low' hrHigh' hr'High'
  have hSub :
      (((interval 0 low).product (interval 0 low)).filter
        (fun u => u.1 ≤ u.2)) ∩
        (((interval 1 high).product (interval 1 high)).filter
          (fun u => u.1 ≤ u.2)) ⊆
      (pairs 0) ∩ (pairs 1) := by
    intro u hu
    obtain ⟨huLow, huHigh⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_biUnion.mpr ⟨low, hlowActive, huLow⟩,
      Finset.mem_biUnion.mpr ⟨high, hhighActive, huHigh⟩⟩
  exact hLocal.trans (Finset.card_le_card hSub)

end ErdosSzekeres
