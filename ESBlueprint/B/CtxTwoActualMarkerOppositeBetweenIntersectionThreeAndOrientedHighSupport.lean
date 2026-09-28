import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenElevenOrActiveStraddlePairIntersectionThree
import ESBlueprint.B.CtxTwoMarkerHighCapacityPairSupportTriangleOfOppositeBetween

set_option maxHeartbeats 12000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- Package the exact actual opposite-between companion residual together with its oriented high-capacity rank-pair support. Besides the transported physical level-one marker, maximum one, independent-fuel/full eleven alternative, exact global-five residual, active low straddle, and intersection cardinality at least three, the high support lies in Q([2,4]) or Q([1,3]) according to the physical order x<p<y or y<p<x.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_intersection_three, ErdosSzekeres.ctx_two_marker_high_capacity_pair_support_triangle_of_opposite_between, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_intersection_three_and_oriented_high_support (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a
  let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q)
  let Q : Finset ℕ → Finset (ℕ × ℕ) := fun S => (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => Q (interval c q))
  (p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨ ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (∃ q ∈ active 0, ∃ r ∈ active 0, q < p ∧ p < r) ∧ 3 ≤ ((pairs 0) ∩ (pairs 1)).card))) ∧ ((x < p ∧ p < y ∧ pairs 1 ⊆ Q (Finset.Icc 2 4)) ∨ (y < p ∧ p < x ∧ pairs 1 ⊆ Q (Finset.Icc 1 3))) := by
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
  let Q : Finset ℕ → Finset (ℕ × ℕ) := fun S =>
    (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun q => Q (interval c q))
  have hClassRaw :=
    ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_intersection_three
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hchosenGlobal
        hopposite hchosen keep m n p high hp hn hhighmem hhigh hbetween
  have hClass : p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧
      (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨
        ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧
         (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧
         (∃ q ∈ active 0, ∃ r ∈ active 0, q < p ∧ p < r) ∧
         3 ≤ ((pairs 0) ∩ (pairs 1)).card)) := by
    cases s <;> cases t <;>
      simpa only [B, rest, capacity, color, support, group, global, active,
        interval, Q, pairs] using hClassRaw
  have hpB := hClass.1
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
  have hOneB : 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_self
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hPosB := ctx_part_positive_letters σ rest t n
  have hChosenGlobalB : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hOppositeB : (match t with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hOrientRaw :=
    ctx_two_marker_high_capacity_pair_support_triangle_of_opposite_between
      B hPosB s t hne (N + 1) (M + 1) x y 1 p hNB hMB (by omega)
        hNsB hMsB hxB hyB (by cases s <;> exact hChosenGlobalB)
        (by cases t <;> exact hOppositeB) hOneB hBsideOne hpB hbetween
  have hOrient :
      (x < p ∧ p < y ∧ pairs 1 ⊆ Q (Finset.Icc 2 4)) ∨
        (y < p ∧ p < x ∧ pairs 1 ⊆ Q (Finset.Icc 1 3)) := by
    cases s <;> cases t <;>
      simpa only [capacity, color, support, group, global, active, interval,
        Q, pairs] using hOrientRaw
  have hResult := And.intro hClass hOrient
  cases s <;> cases t <;>
    simpa only [B, rest, capacity, color, support, group, global, active,
      interval, Q, pairs] using hResult

end ErdosSzekeres
