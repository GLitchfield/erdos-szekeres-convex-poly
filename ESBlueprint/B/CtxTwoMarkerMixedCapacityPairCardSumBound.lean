import ESBlueprint.B.CtxTwoMarkerHighCapacityPruningRankPairBoundOfHighWitness

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- In an exact two-marker chosen-global-five context with a capacity-three witness, the canonical binary low/high capacity pruning bounds every fuel approximation and the full context by the sum of the two exact active opposite-rank pair-support cardinalities. This exposes a direct support-size route to eleven independent of the coarser complete-triangle overlap estimate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness, ErdosSzekeres.ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five, ErdosSzekeres.ctx_point_limits_eq_of_child_interval
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_mixed_capacity_pair_card_sum_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) :
  let capacity : ℕ → ℕ := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p
  let color : ℕ → ℕ := fun p => if capacity p ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun p => color p = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let interval : ℕ → ℕ → Finset ℕ := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun p => ((interval c p).product (interval c p)).filter (fun z => z.1 ≤ z.2))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (pairs 0).card + (pairs 1).card) ∧ σ.bound ≤ (pairs 0).card + (pairs 1).card := by
  classical
  dsimp only
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
  let G := match t, hne, hchosenGlobal, hhigh with
    | Ctx.Side.lower, _, _, _ => σ.u
    | Ctx.Side.upper, _, _, _ => σ.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
    (G - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      (pairs 0).card + (pairs 1).card) ∧
    σ.bound ≤ (pairs 0).card + (pairs 1).card
  have hChosenGlobalPlain : (match s with
      | Ctx.Side.lower => σ.u
      | Ctx.Side.upper => σ.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
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
      σ hpositive s N x hN hNs hx hChosenGlobalPlain color
        ({0, 1} : Finset ℕ) hCover hColor
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hLow : (∀ fuel, Ctx.Context.boundFuel fuel (group 0) ≤ (pairs 0).card) ∧
      (group 0).bound ≤ (pairs 0).card := by
    cases s with
    | lower =>
      cases t with
      | lower => exact (hne rfl).elim
      | upper =>
        simpa [C, color, support, group, G, active, I, Q, pairs] using
          (ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness
            σ hpositive Ctx.Side.lower Ctx.Side.upper hne N M x y high
              hN hM hNM hNs hMs hx hy hchosenGlobal hchosen hhighmem hhigh)
    | upper =>
      cases t with
      | lower =>
        simpa [C, color, support, group, G, active, I, Q, pairs] using
          (ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness
            σ hpositive Ctx.Side.upper Ctx.Side.lower hne N M x y high
              hN hM hNM hNs hMs hx hy hchosenGlobal hchosen hhighmem hhigh)
      | upper => exact (hne rfl).elim
  have hHigh : (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ (pairs 1).card) ∧
      (group 1).bound ≤ (pairs 1).card := by
    cases s with
    | lower =>
      cases t with
      | lower => exact (hne rfl).elim
      | upper =>
        simpa only [C, color, support, group, G, active, I, Q, pairs] using
          (ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness
            σ hpositive Ctx.Side.lower Ctx.Side.upper hne N M x y high
              hN hM hNM hNs hMs hx hy hchosenGlobal hchosen hhighmem hhigh)
    | upper =>
      cases t with
      | lower =>
        simpa only [C, color, support, group, G, active, I, Q, pairs] using
          (ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness
            σ hpositive Ctx.Side.upper Ctx.Side.lower hne N M x y high
              hN hM hNM hNs hMs hx hy hchosenGlobal hchosen hhighmem hhigh)
      | upper => exact (hne rfl).elim
  have hGroups : (group 0).bound + (group 1).bound ≤
      (pairs 0).card + (pairs 1).card :=
    Nat.add_le_add hLow.2 hHigh.2
  constructor
  · intro fuel
    have hh := hDecomp.1 fuel
    simpa using hh.trans hGroups
  · have hh := hDecomp.2
    simpa using hh.trans hGroups

end ErdosSzekeres
