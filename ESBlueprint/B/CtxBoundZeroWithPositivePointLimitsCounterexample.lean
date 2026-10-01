import ESBlueprint.B.CtxBoundZeroOfBothSidesLargeSiblingMaxima

namespace ErdosSzekeres

/-- There is a well-formed multi-run context with full recursive bound zero and an actual child with positive cup and cap point limits. The explicit k=4 two-axis saturated witness has word S,1L,S,2U,S and maxima 2,2. Refutes the tempting generic lower-bound shortcut from point activity to positive full context bound; does not refute maximal-segment exchange. Uses the closed both-axis multi-run zero theorem, and ordinary finite arithmetic for the witness capacities.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_zero_of_both_sides_large_sibling_maxima
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_zero_with_positive_point_limits_counterexample : ∃ σ : Ctx.Context, σ.WellFormed ∧ 2 ≤ σ.numRuns ∧ σ.bound = 0 ∧ ∃ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
  classical
  let σ : Ctx.Context :=
    { a := 4, u := 4, k := 4,
      word := [.child, .ext 1 .lower, .child, .ext 2 .upper, .child],
      maxima := [2, 2] }
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p j v hp
      have hplen : p < 5 := by
        by_contra h
        have hletter := Ctx.Context.letterAt_of_length_le σ
          (show σ.word.length ≤ p by change 5 ≤ p; omega)
        rw [hletter] at hp
        cases hp
      have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 2 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
  have hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    exact (hwf.2.2.2.2.2 p j v hp).1
  have hruns : 2 ≤ σ.numRuns := by decide
  have hL : 1 ∈ σ.levelsOn .lower 0 := by decide
  have hU : 2 ∈ σ.levelsOn .upper 0 := by decide
  have hzero : σ.bound = 0 :=
    ctx_bound_zero_of_both_sides_large_sibling_maxima σ hpositive hruns 1 2 hL hU
      (by decide) (by decide)
  refine ⟨σ, hwf, hruns, hzero, 0, ?_, ?_, ?_⟩ <;> decide

end ErdosSzekeres
