import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- A well-formed context at (3,3,3) whose interval recurrence retains a zero-child cut with positive sibling. This certifies the zero-bound case omitted by the historical Python F2 recursion and guards the exact additivity falsifier.
@node
@ws B
@kind formalization
@dangling-ok Executable regression for the context-additivity falsifier: the historical positive-child recurrence assigns zero to this context, whereas Lean retains its 0+1 cut. -/
theorem ctx_bound_zero_child_regression : let σ : Ctx.Context := ⟨3, 3, 3,
    [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child], [1]⟩
  σ.WellFormed ∧
    (σ.part [0] Ctx.Side.lower 1).bound = 0 ∧
    (σ.part [2] Ctx.Side.upper 1).bound = 1 ∧ σ.bound = 1 := by
  dsimp only
  constructor
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp
    · intro p l s h
      have hp : p < 3 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 3 ≤ p by omega)] at h
        cases h
      interval_cases p <;> simp [Ctx.Context.letterAt] at h
      rcases h with ⟨rfl, rfl⟩
      decide
  · decide

end ErdosSzekeres
