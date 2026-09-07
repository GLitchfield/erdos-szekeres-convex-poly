import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- An unused external level still contributes its sibling maximum to the Lean join limit. A well-formed two-child context with no external letters has bound one; omitting its unused level incorrectly gives two. Regression for the exact additivity falsifier domain.
@node
@ws B
@kind formalization
@dangling-ok Executable regression for Lean/Python context semantics: WellFormed permits unused levels in maxima, which the earlier Python limit computation skipped. -/
theorem ctx_unused_level_regression : let σ : Ctx.Context := ⟨3, 3, 3, [Ctx.Letter.child, Ctx.Letter.child], [1]⟩
    σ.WellFormed ∧ σ.extPositions 1 = [] ∧ σ.cupLimit 0 0 = 1 ∧
      σ.capLimit 0 0 = 2 ∧ σ.bound = 1 := by
  dsimp only
  constructor
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp
    · intro p l s h
      have hp : p < 2 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 2 ≤ p by omega)] at h
        cases h
      interval_cases p <;> simp [Ctx.Context.letterAt] at h
  · decide

end ErdosSzekeres
