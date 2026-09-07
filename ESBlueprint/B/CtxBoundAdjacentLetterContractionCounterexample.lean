import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Adjacent identical-letter contraction is false for well-formed contexts. The context with parameters (5,5,6), word [child, ext 1 lower, ext 2 upper, child, child], and maxima [1,1] has bound 12; deleting its final child produces bound 9. This refutes the unrestricted contraction law proposed as a reduction for single-run sandwich additivity.
@node
@ws B
@kind refutation
@consumer ErdosSzekeres.ctx_bound_adjacent_letter_contraction -/
theorem ctx_bound_adjacent_letter_contraction_counterexample : ¬ (∀ (σ : Ctx.Context), σ.WellFormed →
  ∀ (left right : List Ctx.Letter) (letter : Ctx.Letter),
    σ.word = left ++ [letter, letter] ++ right →
      σ.bound = ({ σ with word := left ++ [letter] ++ right } : Ctx.Context).bound) := by
  intro h
  let σ : Ctx.Context := ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 2 Ctx.Side.upper,
      Ctx.Letter.child, Ctx.Letter.child], [1, 1]⟩
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p l s hletter
      have hp : p < 5 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _ (show 5 ≤ p by omega)] at hletter
        cases hletter
      interval_cases p <;> simp [σ, Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  have hlarge : σ.bound = 12 := by
    set_option maxRecDepth 10000 in decide
  have hsmall : ({ σ with word :=
      [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 2 Ctx.Side.upper,
        Ctx.Letter.child] } : Ctx.Context).bound = 9 := by
    set_option maxRecDepth 10000 in decide
  specialize h σ hwf
    [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 2 Ctx.Side.upper]
    [] Ctx.Letter.child rfl
  change σ.bound = ({ σ with word :=
    [Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 2 Ctx.Side.upper,
      Ctx.Letter.child] } : Ctx.Context).bound at h
  omega

end ErdosSzekeres
