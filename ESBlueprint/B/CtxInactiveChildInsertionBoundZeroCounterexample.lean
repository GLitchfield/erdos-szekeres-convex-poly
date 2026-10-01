import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- Replacing one interior repeated marker by an inactive child can lower the recursive bound even when surviving child capacities stay unchanged. Explicit well-formed globals4/4/4, maxima2,1,1,1, old word1L,2U,1L,1L,3U,4L,S and new word1L,2U,S,1L,3U,4L,S. Old child6 has cup and cap one and full bound one; the inserted child2 has zero cup, old child6 keeps both unit capacities, but the new two-run context has bound zero. Documents why exterior point stability and zero-capacity insertion alone cannot provide a recursive lower transport for maximal-segment exchange. Does not contradict the closed marker-subset comparison with its stronger hypotheses.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_inactive_child_insertion_bound_zero_counterexample : ∃ σ τ : Ctx.Context, σ.WellFormed ∧ τ.WellFormed ∧ σ.a = 4 ∧ σ.u = 4 ∧ σ.k = 4 ∧ τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧ σ.maxima = [2, 1, 1, 1] ∧ τ.maxima = σ.maxima ∧ σ.word = [Ctx.Letter.ext 1 .lower, Ctx.Letter.ext 2 .upper, Ctx.Letter.ext 1 .lower, Ctx.Letter.ext 1 .lower, Ctx.Letter.ext 3 .upper, Ctx.Letter.ext 4 .lower, Ctx.Letter.child] ∧ τ.word = σ.word.set 2 Ctx.Letter.child ∧ σ.childPositions = [6] ∧ τ.childPositions = [2, 6] ∧ 2 ≤ τ.numRuns ∧ τ.cupLimit 2 2 = 0 ∧ τ.capLimit 2 2 = 1 ∧ σ.cupLimit 6 6 = 1 ∧ σ.capLimit 6 6 = 1 ∧ τ.cupLimit 6 6 = 1 ∧ τ.capLimit 6 6 = 1 ∧ σ.bound = 1 ∧ τ.bound = 0 := by
  let σ : Ctx.Context :=
    { a := 4, u := 4, k := 4,
      word := [.ext 1 .lower, .ext 2 .upper, .ext 1 .lower,
        .ext 1 .lower, .ext 3 .upper, .ext 4 .lower, .child],
      maxima := [2, 1, 1, 1] }
  let τ : Ctx.Context := { σ with word := σ.word.set 2 Ctx.Letter.child }
  have hwfσ : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p j v hp
      have hplen : p < 7 := by
        by_contra h
        have hletter := Ctx.Context.letterAt_of_length_le σ
          (show σ.word.length ≤ p by change 7 ≤ p; omega)
        rw [hletter] at hp
        cases hp
      have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 2 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 3 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 4 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
  have hwfτ : τ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [τ, σ]
    · intro p j v hp
      have hplen : p < 7 := by
        by_contra h
        have hletter := Ctx.Context.letterAt_of_length_le τ
          (show τ.word.length ≤ p by change 7 ≤ p; omega)
        rw [hletter] at hp
        cases hp
      have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 2 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 3 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 4 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
  refine ⟨σ, τ, hwfσ, hwfτ, ?_⟩
  decide

end ErdosSzekeres
