import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- PEEL: every well-formed context with globals at least four, at least two child runs, legal sibling maxima and bound at least two attains its full recursive bound by peeling some child on some side with a legal coupling. Children in the interior of a run are allowed; extreme and run-end restrictions have k6 diagnostic failures. The proposed mechanism chooses the oldest new child marker with least cost to binding chains in the remainder.
@node
@ws B
@kind conjecture
@dangling-ok Approved R19 all-context singleton normal form generalizing the closed at-most-three-child base and N_root; cost-based selection remains open
@falsifier ctx_bound_singleton_attainment.py -/
theorem ctx_bound_attained_by_singleton_cut (σ : Ctx.Context) (hwf : σ.WellFormed) (ha : 4 ≤ σ.a) (hu : 4 ≤ σ.u)
(hruns : 2 ≤ σ.numRuns) (hb : 2 ≤ σ.bound) :
∃ p ∈ σ.childPositions, ∃ (s : Ctx.Side) (c : ℕ),
  1 ≤ c ∧ c ≤ σ.k - 2 ∧
  σ.bound = (σ.part [p] s c).bound +
    (σ.part (σ.childPositions.filter (fun q => q ≠ p))
      (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
      (σ.k - 1 - c)).bound := by
  sorry

end ErdosSzekeres
