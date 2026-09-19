import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenElevenOrActiveStraddlePairCollisions
import ESBlueprint.B.CtxTwoMarkerTwoPairCollisionIntersectionThree

set_option maxHeartbeats 12000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- The actual opposite-between companion is bounded by eleven unless both globals equal five, active low-capacity children straddle its physical level-one marker, and the canonical low/high active rank-pair intersection has cardinality at least three. Two-marker collision amplification eliminates the exact-cardinality-two residual while retaining the marker occurrence, maximum one, every fuel, arbitrary histories, and both orientations.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_collisions, ErdosSzekeres.ctx_two_marker_two_pair_collision_intersection_three, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_intersection_three (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a
  let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => ((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))
  p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨ ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (∃ q ∈ active 0, ∃ r ∈ active 0, q < p ∧ p < r) ∧ 3 ≤ ((pairs 0) ∩ (pairs 1)).card)) := by
  classical
  dsimp only
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  let capacity : ℕ → ℕ := fun q => match s with
    | Ctx.Side.lower => B.cupLimit q q
    | Ctx.Side.upper => B.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c =>
    B.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global : ℕ :=
    match t, hne, hchosenGlobal, hopposite, hhighmem, hhigh with
    | Ctx.Side.lower, _, _, _, _, _ => B.u
    | Ctx.Side.upper, _, _, _, _, _ => B.a
  let active : ℕ → Finset ℕ := fun c =>
    (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q =>
    Finset.Icc ((group c).leftExt t 0 q + 1)
      (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun q =>
      (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)))
  have hClass :=
    ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_collisions
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hchosenGlobal
        hopposite hchosen keep m n p high hp hn hhighmem hhigh hbetween
  obtain ⟨hpB, hmax, hcase⟩ := hClass
  refine ⟨hpB, hmax, ?_⟩
  rcases hcase with hbound | hresidual
  · exact Or.inl hbound
  right
  refine ⟨hresidual.1, hresidual.2.1, hresidual.2.2.1, ?_⟩
  have hTwoLocal : 2 ≤ ((pairs 0) ∩ (pairs 1)).card := by
    cases s <;> cases t <;>
      simpa only [B, rest, capacity, color, support, group, global, active,
        interval, pairs] using hresidual.2.2.2
  have hOneLt : 1 < ((pairs 0) ∩ (pairs 1)).card := by
    omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp hOneLt
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNB : N + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMB : M + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsB : B.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hNpos).trans hNs
  have hMsB : B.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hMpos).trans hMs
  have hxB : x ∈ B.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hNpos]
    exact hx
  have hyB : y ∈ B.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hMpos]
    exact hy
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hChosenB : ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j,
      z = x ∨ z = y := by
    have hs : B.sideAt 1 ≠ s := by
      rw [hBsideOne]
      exact Ne.symm hne
    intro j hj z hz
    rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [Ctx.Context.part_extPositions_succ σ rest t n
      (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
    exact hchosen i hi z hz
  have hPosB := ctx_part_positive_letters σ rest t n
  have hGlobalB : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := hresidual.1.le
  have hThree := ctx_two_marker_two_pair_collision_intersection_three
    B hPosB s t (N + 1) (M + 1) x y hNB hMB (by omega)
      hNsB hMsB hxB hyB (by cases s <;> exact hGlobalB) hChosenB
  have hThreeLocal : ∀ z ∈ (pairs 0) ∩ (pairs 1),
      ∀ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w →
        3 ≤ ((pairs 0) ∩ (pairs 1)).card := by
    cases s <;> cases t <;>
      simpa only [capacity, color, support, group, global, active, interval,
        pairs] using hThree
  have hResult := hThreeLocal z hz w hw hzw
  cases s <;> cases t <;>
    simpa only [B, rest, capacity, color, support, group, global, active,
      interval, pairs] using hResult

end ErdosSzekeres
