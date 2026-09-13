import ESBlueprint.B.CtxAxisRegionLimitsExact

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Pointwise cup and cap limits are constant across an uninterrupted interval of physical child positions. With no external marker between the endpoints, every level filter seen by the left and right extension folds agrees; hence the pure extensions, joined extensions and both endpoint capacities agree. This supplies the canonical run-constant coloring by chosen capacity needed by the global-five capacity-three pruning decomposition. Exact search in runs/sol-12h/search-point-limits-child-interval.json found no duplicate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_point_limits_eq_of_child_interval (σ : Ctx.Context) (p q : ℕ) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (hpq : p ≤ q) (hinterval : ∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) : σ.cupLimit p p = σ.cupLimit q q ∧ σ.capLimit p p = σ.capLimit q q := by
  classical
  have hextOutside (N z : ℕ) (hz : z ∈ σ.extPositions N) : z < p ∨ q < z := by
    by_contra hout
    have hc := hinterval z (by omega) (by omega)
    have hletter : σ.letterAt z = Letter.child :=
      of_decide_eq_true (List.mem_filter.mp hc).2
    simp [extPositions, hletter] at hz
  have hregion (s : Side) : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
      (z < p ↔ z < q) ∧ (p < z ↔ q < z) := by
    intro j _ z hz
    have hout := hextOutside j z hz
    constructor <;> constructor <;> intro h <;> omega
  have hl := ctx_axis_region_limits_exact σ Side.lower p q (hregion Side.lower)
  have hu := ctx_axis_region_limits_exact σ Side.upper p q (hregion Side.upper)
  exact ⟨by simpa using hl.2.2.2, by simpa using hu.2.2.2⟩


end ErdosSzekeres
