import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Boundary domination for two-run contexts (Gavin and Codex, 7 September): for a well-formed context with exactly two child runs, every nonempty proper partition of the child positions, in either orientation and at any admissible coupling d, is dominated by a prefix or suffix cut in the same orientation at some admissible coupling d'. With ctx_bound_cut_le this gives additivity for every two-run context. Changing the coupling is essential: keeping d has counterexamples (ctx_bound_same_size_exchange_counterexample). Evidence: zero failures of the candidate on every partition of every context up to five letters at k = 5 and four letters at k = 6, all run counts (experiment 0121 addendum 6); the falsifier re-checks the two-run case. First milestone: the A-B-A-B membership pattern.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_cut_le, ErdosSzekeres.ctx_bound_additive_prefix_suffix
@consumer ErdosSzekeres.ctx_bound_additive_multi_run
@falsifier ctx_two_run_boundary.py -/
theorem ctx_bound_two_run_boundary_domination (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns = 2) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (∃ I d', (∃ j, 0 < j ∧ j < σ.childPositions.length ∧ (I = σ.childPositions.take j ∨ I = σ.childPositions.drop j)) ∧ 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧ (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ (σ.part I Ctx.Side.lower d').bound + (σ.part (σ.childPositions.filter (fun p => p ∉ I)) Ctx.Side.upper (σ.k - 1 - d')).bound) ∧ (∃ I d', (∃ j, 0 < j ∧ j < σ.childPositions.length ∧ (I = σ.childPositions.take j ∨ I = σ.childPositions.drop j)) ∧ 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ (σ.part I Ctx.Side.upper (σ.k - 1 - d')).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ I)) Ctx.Side.lower d').bound) := by
  sorry

end ErdosSzekeres
