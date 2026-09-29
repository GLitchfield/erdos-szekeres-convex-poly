import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- End-cut normal form restricted to both global parameters at least four: for a well-formed context with at least two child runs and 4 <= a, 4 <= u, the bound is attained by a cut that isolates the first or the last child position, on some side at some admissible coupling. The unrestricted form ctx_bound_attained_by_end_cut is false at a = 3 (ctx_bound_attained_by_end_cut_counterexample) and, by the cap/cup mirror, at u = 3. Evidence: every multi-run context with at most four child letters and two external levels at (4,4,5), (4,5,5), (5,5,5), (4,5,6), (5,5,6), (4,6,6), (6,6,6), (4,5,7), (5,6,7) and (4,7,7) (Claude run claude-uniform-mechanism-20260928, Track A, END column). It keeps the end-strip route of experiment 0124 available above the small-capacity boundary.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_two_run_boundary_domination
@falsifier ctx_end_cut_normal_form_four.py -/
theorem ctx_bound_attained_by_end_cut_of_four_le (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns) (ha : 4 ≤ σ.a) (hu : 4 ≤ σ.u) : ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧ ∃ d, 1 ≤ d ∧ d ≤ σ.k - 2 ∧ (σ.bound ≤ (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨ σ.bound ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound) := by
  sorry

end ErdosSzekeres
