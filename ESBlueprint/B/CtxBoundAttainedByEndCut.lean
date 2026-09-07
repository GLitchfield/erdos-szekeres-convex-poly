import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- End-cut normal form for the context bound (experiment 0124 §2c): for a well-formed context with at least two child runs, the bound, which is the maximum over all interval cuts, is attained by a cut that isolates the first or the last child position, on some side at some admissible coupling. Interior blocks never win. Consequences: bound has a recursion over end cuts only, every cut tree normalizes to a sequence of end strips, and the exchange lemma behind additivity (the two-run boundary domination) becomes a commutation of two end strips. Evidence: every one of the 2,600 contexts with two or three runs and nonzero bound at k = 6 with up to four letters and two levels; the falsifier re-checks five cases.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_two_run_boundary_domination
@falsifier ctx_end_cut_normal_form.py -/
theorem ctx_bound_attained_by_end_cut (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns) : ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧ ∃ d, 1 ≤ d ∧ d ≤ σ.k - 2 ∧ (σ.bound ≤ (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨ σ.bound ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound) := by
  sorry

end ErdosSzekeres
