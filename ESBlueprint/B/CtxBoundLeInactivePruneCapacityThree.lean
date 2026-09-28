import ESBlueprint.B.CtxAxisRegionLimitsExact
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Deleting all inactive children by original-history pruning cannot lower the full context bound when every original child has minimum point capacity at most three. Every source fuel approximation is bounded by the full pruned bound. Positive labels suffice, empty active support is included, and all indexed history is preserved. Activity is constant on each physical child run, so the capacity-three run-group decomposition separates live and dead children; the dead group vanishes by the sum-of-point-bases bound. Removes the capacity-two-only deletion dependency in prospective active boundary rank-pair estimates.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_inactive_prune_capacity_three (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (hsmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3) :
  let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let τ : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound := by
  classical
  let live (p : ℕ) := 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p
  let keep := σ.childPositions.filter live
  let τ : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  let color (p : ℕ) := if live p then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound
  have hSupport : support 0 = keep := by
    apply List.filter_congr
    intro p hp
    by_cases hlive : live p <;> simp only [color, hlive, if_true, if_false] <;> simp
  have hGroup : group 0 = τ := by simp only [group, hSupport]; rfl
  have hColor : ∀ a ∈ σ.childPositions, ∀ b ∈ σ.childPositions, a ≤ b →
      (∀ r, a ≤ r → r ≤ b → r ∈ σ.childPositions) → color a = color b := by
    intro a ha b hb hab hbetween
    have hRegion (s : Side) : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
        (z < a ↔ z < b) ∧ (a < z ↔ b < z) := by
      intro j hj z hz
      have hOutside : z < a ∨ b < z := by
        by_contra h
        have hzc := hbetween z (by omega) (by omega)
        have hc := of_decide_eq_true (List.mem_filter.mp hzc).2
        have he := (List.mem_filter.mp hz).2
        simp [hc] at he
      omega
    have hc := (ctx_axis_region_limits_exact σ Side.lower a b (hRegion Side.lower)).2.2.2
    have hp := (ctx_axis_region_limits_exact σ Side.upper a b (hRegion Side.upper)).2.2.2
    simp only [color, live, hc, hp]
  have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hZero : (group 1).bound = 0 := by
    have hz : ∀ p ∈ (group 1).childPositions,
        (group 1).cupLimit p p = 0 ∨ (group 1).capLimit p p = 0 := by
      intro p hp
      have ht := ctx_part_pruning_history_transport σ hpositive (support 1) Side.lower 0
      have hChild : (group 1).childPositions = σ.childPositions.filter (· ∈ support 1) := ht.2.1
      rw [hChild] at hp
      have hsp : p ∈ support 1 := of_decide_eq_true (List.mem_filter.mp hp).2
      have hc : color p = 1 := of_decide_eq_true (List.mem_filter.mp hsp).2
      have hdead : ¬ live p := by
        intro hlive
        simp only [color, if_pos hlive] at hc
        omega
      have hlimits : (group 1).cupLimit p p = σ.cupLimit p p ∧
          (group 1).capLimit p p = σ.capLimit p p := ht.2.2.2.2.2.1 p p
      rw [hlimits.1, hlimits.2]
      dsimp only [live] at hdead
      omega
    have hs : ((group 1).childPositions.map
        (fun p => baseOf ((group 1).cupLimit p p) ((group 1).capLimit p p) (group 1).k)).sum = 0 := by
      apply List.sum_eq_zero
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      simp only [baseOf, if_pos (hz p hp)]
    exact Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases (group 1)).trans_eq hs)
  have hTotal : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) = τ.bound := by
    simp [hZero, hGroup]
  have hd := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color {0, 1}
    hCover hsmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
    σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hd
  simpa only [hTotal] using hd

end ErdosSzekeres
