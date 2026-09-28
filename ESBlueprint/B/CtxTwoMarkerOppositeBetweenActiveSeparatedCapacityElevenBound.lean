import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningFiveBoundOfActiveOppositeBoundary
import ESBlueprint.B.CtxTwoMarkerOppositeBetweenSeparatedCapacityElevenBound

namespace ErdosSzekeres

/-- The two-marker low/high decomposition has bound eleven when the actual opposite marker lies to one side of every active child in the low-capacity pruning; inactive low children are harmless by the active low-five theorem.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_low_capacity_pruning_five_bound_of_active_opposite_boundary, ErdosSzekeres.ctx_two_marker_high_capacity_pruning_six_bound_of_opposite_between, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five, ErdosSzekeres.ctx_point_limits_eq_of_child_interval
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_opposite_between_active_separated_capacity_eleven_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high L z : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ w ∈ σ.extPositions j, w = x ∨ w = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) (hL : L ∈ σ.levels) (hLt : σ.sideAt L = t) (hz : z ∈ σ.extPositions L) (hLM : L < M) (hbetween : (x < z ∧ z < y) ∨ (y < z ∧ z < x)) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let color := fun p => if capacity p ≤ 2 then (0 : ℕ) else 1; let support := fun c => σ.childPositions.filter (fun p => color p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); ((∀ q ∈ (group 0).childPositions, 0 < (group 0).cupLimit q q ∧ 0 < (group 0).capLimit q q → q < z) ∨ (∀ q ∈ (group 0).childPositions, 0 < (group 0).cupLimit q q ∧ 0 < (group 0).capLimit q q → z < q)) → (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 11) ∧ σ.bound ≤ 11 := by
  classical
  let C (p : ℕ) := match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let color (p : ℕ) := if C p ≤ 2 then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  change ((∀ q ∈ (group 0).childPositions,
      0 < (group 0).cupLimit q q ∧ 0 < (group 0).capLimit q q → q < z) ∨
      (∀ q ∈ (group 0).childPositions,
        0 < (group 0).cupLimit q q ∧ 0 < (group 0).capLimit q q → z < q)) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 11) ∧ σ.bound ≤ 11
  intro hboundary
  have hCover : ∀ p ∈ σ.childPositions,
      color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      p ≤ q → (∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) →
      color p = color q := by
    intro p hp q hq hpq hinterval
    have hh := ctx_point_limits_eq_of_child_interval σ p q hp hq hpq hinterval
    have hC : C p = C q := by
      cases s with
      | lower => simpa only [C] using hh.1
      | upper => simpa only [C] using hh.2
    simp only [color, hC]
  have hDecomp :=
    ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
      σ hpositive s N x hN hNs hx hchosenGlobal color ({0, 1} : Finset ℕ)
      hCover hColor
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hBoundaryLow :
      let lowSupport := σ.childPositions.filter (fun p => C p ≤ 2)
      let low : Ctx.Context := { σ with
        word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
          | Ctx.Letter.child => if p ∈ lowSupport then Ctx.Letter.child
              else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
          | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
      (∀ q ∈ low.childPositions,
          0 < low.cupLimit q q ∧ 0 < low.capLimit q q → q < z) ∨
        (∀ q ∈ low.childPositions,
          0 < low.cupLimit q q ∧ 0 < low.capLimit q q → z < q) := by
    simpa [C, color, support, group] using hboundary
  have hLow : (∀ fuel, Ctx.Context.boundFuel fuel (group 0) ≤ 5) ∧
      (group 0).bound ≤ 5 := by
    have hh :=
      ctx_two_marker_low_capacity_pruning_five_bound_of_active_opposite_boundary
        σ hpositive s t hne N M x y high L z hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen hhighmem hhigh hL hLt hz hLM
    have hh' := hh hBoundaryLow
    simpa [C, color, support, group] using hh'
  have hHigh : (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ 6) ∧
      (group 1).bound ≤ 6 := by
    have hh := ctx_two_marker_high_capacity_pruning_six_bound_of_opposite_between
      σ hpositive s t hne N M x y L z hN hM hNM hNs hMs hx hy
      hchosenGlobal hopposite hchosen hL hLt hz hbetween
    simpa [C, color, support, group] using hh
  have hGroups : (group 0).bound + (group 1).bound ≤ 11 := by
    omega
  constructor
  · intro fuel
    have hh := hDecomp.1 fuel
    simpa using hh.trans hGroups
  · have hh := hDecomp.2
    simpa using hh.trans hGroups

end ErdosSzekeres
