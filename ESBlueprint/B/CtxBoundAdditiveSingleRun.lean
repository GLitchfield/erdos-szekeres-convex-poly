import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Additivity of the context bound for a single-run context: the bound is the classical threshold with the run internal limits, and every partition of the run (any interleaving), both orientations and every coupling d, gives part bounds summing to at most it. This is the Baek-Balko one-level inequality with the full positional context (experiments 0118, 0120-0122); the falsifier is the general additivity test, which covers this case.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive
@falsifier ctx_bound_additive.py -/
theorem ctx_bound_additive_single_run (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
