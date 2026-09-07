import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- A genuine alternating partition of a two-run context beats every interval competitor that preserves its cardinality, orientation, and coupling simultaneously. Both the kept side and its complement are noninterval. This explicit witness rules out that restricted exchange rule; it does not refute unrestricted exchange or context additivity.
@node
@ws B
@kind refutation
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_same_size_exchange_counterexample : let σ : Ctx.Context := ⟨4, 4, 5,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
     Ctx.Letter.child, Ctx.Letter.child], [1]⟩
  let keep : List ℕ := [0, 3]
  let value (block : List ℕ) := (σ.part block Ctx.Side.upper 1).bound +
    (σ.part (σ.childPositions.filter (fun p ↦ p ∉ block)) Ctx.Side.lower 3).bound
  σ.WellFormed ∧ σ.childPositions = [0, 1, 3, 4] ∧ σ.numRuns = 2 ∧
    keep ∉ σ.blocks ∧ (σ.childPositions.filter (fun p ↦ p ∉ keep)) ∉ σ.blocks ∧
    keep.length = 2 ∧ value keep = 4 ∧
    (∀ block ∈ σ.blocks, block.length = keep.length → value block ≤ 3) := by
  dsimp only
  constructor
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp
    · intro p l s h
      have hp : p < 5 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 5 ≤ p by omega)] at h
        cases h
      interval_cases p <;> simp [Ctx.Context.letterAt] at h
      rcases h with ⟨rfl, rfl⟩
      decide
  · decide

end ErdosSzekeres
