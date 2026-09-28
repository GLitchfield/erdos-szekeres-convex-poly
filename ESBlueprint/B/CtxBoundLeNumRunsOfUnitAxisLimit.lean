import ESBlueprint.B.CtxUnitAxisActiveRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- If either pointwise cup capacity or pointwise cap capacity is at most one at every child, every fuel approximation and the full recursive bound are at most the number of child runs. Uses an active-region count separated by external positions on the chosen side; strict capacity loss excludes a region contributing to both parts. Positive external labels suffice; no run-length or well-formedness restriction. Intended to control arbitrarily long outer blocks in the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_numRuns_of_unit_axis_limit (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (s : Ctx.Side)
  (hunit : ∀ p ∈ σ.childPositions,
    (match s with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) ≤ 1) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ σ.numRuns) ∧ σ.bound ≤ σ.numRuns := by
  have h := ctx_unit_axis_active_region_potential σ hpositive s hunit
  exact ⟨fun fuel => (h.1 fuel).trans h.2.2, h.2.1.trans h.2.2⟩

end ErdosSzekeres
