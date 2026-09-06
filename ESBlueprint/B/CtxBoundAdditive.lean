import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Additivity of the context bound (the open lemma of the induction, experiments 0120-0121): for every well-formed context, every partition of its child letters into a kept part and the rest (any interleaving), both orientations and every coupling d, the two part bounds sum to at most the bound of the whole. Tested with no violation on about 1.5 million interleaved partitions over eight parameter triples, including the k = 6 contexts where run-boundary cuts alone fail.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_card_le_bound
@falsifier ctx_bound_additive.py -/
theorem ctx_bound_additive (σ : Ctx.Context) (hwf : σ.WellFormed) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
