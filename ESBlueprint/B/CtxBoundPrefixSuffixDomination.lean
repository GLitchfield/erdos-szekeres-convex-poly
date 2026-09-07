import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Prefix/suffix domination in every context (experiment 0121 addendum 6, 0124): for a well-formed context, every nonempty proper partition of the child positions that is not itself a prefix or suffix cut, in either orientation and at any admissible coupling d, is dominated by a prefix or suffix cut in the same orientation at some admissible coupling d'. With ctx_bound_cut_le, ctx_bound_additive_prefix_suffix and ctx_bound_interval_or_complement_le this is both additivity conjectures. Generalizes ctx_bound_two_run_boundary_domination to any number of runs and covers the single-run sandwich. Evidence: zero failures on every partition of every context up to five letters at k = 5 and four letters at k = 6, seven cases, 155,472 to 288,408 oriented partitions each; keeping the coupling fails thousands of times.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_cut_le, ErdosSzekeres.ctx_bound_additive_prefix_suffix, ErdosSzekeres.ctx_bound_interval_or_complement_le
@consumer ErdosSzekeres.ctx_bound_additive
@falsifier ctx_prefix_suffix_domination.py -/
theorem ctx_bound_prefix_suffix_domination (σ : Ctx.Context) (hwf : σ.WellFormed) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (∃ I d', (∃ j, 0 < j ∧ j < σ.childPositions.length ∧ (I = σ.childPositions.take j ∨ I = σ.childPositions.drop j)) ∧ 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧ (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ (σ.part I Ctx.Side.lower d').bound + (σ.part (σ.childPositions.filter (fun p => p ∉ I)) Ctx.Side.upper (σ.k - 1 - d')).bound) ∧ (∃ I d', (∃ j, 0 < j ∧ j < σ.childPositions.length ∧ (I = σ.childPositions.take j ∨ I = σ.childPositions.drop j)) ∧ 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ (σ.part I Ctx.Side.upper (σ.k - 1 - d')).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ I)) Ctx.Side.lower d').bound) := by
  sorry

end ErdosSzekeres
