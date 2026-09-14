import ESBlueprint.B.CtxCapacityThreeChildrenExteriorOfTwoLevelsGlobalFive
import ESBlueprint.B.CtxPartPruningHistoryTransport

namespace ErdosSzekeres

/-- The canonical original-history pruning selected by chosen-axis capacity exactly three has precisely the source capacity-three children, and with two actual chosen levels at global at most five all of those children lie in one common exterior region in the pruning own preserved indexed history. Checked pruning transport supplies exact child support, levels and marker positions; the global-five capacity-three geometry supplies the orientation. This turns the residual high-capacity summand into a boundary-ready context. Exact searches in runs/sol-12h/search-capacity-three-pruning-exterior.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_capacity_three_pruning_exterior_of_two_levels_global_five (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let support := σ.childPositions.filter (fun p => capacity p = 3); let group := ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); (∀ p, p ∈ group.childPositions ↔ p ∈ σ.childPositions ∧ capacity p = 3) ∧ ((x < y ∧ ∀ p ∈ group.childPositions, ∀ j ∈ group.levelsOn s 0, ∀ z ∈ group.extPositions j, z < p) ∨ (y < x ∧ ∀ p ∈ group.childPositions, ∀ j ∈ group.levelsOn s 0, ∀ z ∈ group.extPositions j, p < z)) := by
  classical
  let capacity := fun p => match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let support := σ.childPositions.filter (fun p => capacity p = 3)
  let group : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  change (∀ p, p ∈ group.childPositions ↔
      p ∈ σ.childPositions ∧ capacity p = 3) ∧
    ((x < y ∧ ∀ p ∈ group.childPositions,
      ∀ j ∈ group.levelsOn s 0, ∀ z ∈ group.extPositions j, z < p) ∨
    (y < x ∧ ∀ p ∈ group.childPositions,
      ∀ j ∈ group.levelsOn s 0, ∀ z ∈ group.extPositions j, p < z))
  have ht := ctx_part_pruning_history_transport σ hpositive support Ctx.Side.lower 0
  have hChild : group.childPositions = σ.childPositions.filter (· ∈ support) := by
    simpa only [group] using ht.2.1
  have hLevels (v : Ctx.Side) (top : ℕ) :
      group.levelsOn v top = σ.levelsOn v top := by
    simpa only [group] using ht.2.2.2.1 v top
  have hExt (j : ℕ) (hj : j ∈ σ.levels) :
      group.extPositions j = σ.extPositions j := by
    simpa only [group] using (ht.2.2.1 j hj).1
  have hChildIff (p : ℕ) : p ∈ group.childPositions ↔
      p ∈ σ.childPositions ∧ capacity p = 3 := by
    rw [hChild]
    simp only [List.mem_filter, decide_eq_true_eq, support]
    tauto
  have hGeom := ctx_capacity_three_children_exterior_of_two_levels_global_five
    σ s N M x y hN hM hNM hNs hMs hx hy hglobal
  refine ⟨hChildIff, ?_⟩
  rcases hGeom with hl | hr
  · refine Or.inl ⟨hl.1, ?_⟩
    intro p hp j hj z hz
    have hps := (hChildIff p).mp hp
    have hcap : 3 ≤ (match s with
        | Ctx.Side.lower => σ.cupLimit p p
        | Ctx.Side.upper => σ.capLimit p p) := by
      have : 3 ≤ capacity p := by omega
      simpa only [capacity] using this
    have hjSource : j ∈ σ.levelsOn s 0 := by simpa only [hLevels] using hj
    have hjLevel : j ∈ σ.levels := (List.mem_filter.mp hjSource).1
    have hzSource : z ∈ σ.extPositions j := by simpa only [hExt j hjLevel] using hz
    exact hl.2 p hps.1 hcap j hjSource z hzSource
  · refine Or.inr ⟨hr.1, ?_⟩
    intro p hp j hj z hz
    have hps := (hChildIff p).mp hp
    have hcap : 3 ≤ (match s with
        | Ctx.Side.lower => σ.cupLimit p p
        | Ctx.Side.upper => σ.capLimit p p) := by
      have : 3 ≤ capacity p := by omega
      simpa only [capacity] using this
    have hjSource : j ∈ σ.levelsOn s 0 := by simpa only [hLevels] using hj
    have hjLevel : j ∈ σ.levels := (List.mem_filter.mp hjSource).1
    have hzSource : z ∈ σ.extPositions j := by simpa only [hExt j hjLevel] using hz
    exact hr.2 p hps.1 hcap j hjSource z hzSource


end ErdosSzekeres
