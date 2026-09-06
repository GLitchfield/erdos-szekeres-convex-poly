import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Additivity of the context bound for a context with at least two runs, where the bound is the maximum over interval cuts: an arbitrary partition (any interleaving) is dominated by that maximum. For an interval partition this is ctx_bound_cut_le; the content is the exchange argument of experiment 0121 for interleaved partitions. The falsifier is the general additivity test, which covers this case.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive
@falsifier ctx_bound_additive.py -/
theorem ctx_bound_additive_multi_run (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
