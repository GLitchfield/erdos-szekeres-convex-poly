import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A well-formed 4/4/4 two-run context has every indexed sibling maximum equal to one and both point capacities exactly one at every actual child, yet its full recursive bound equals zero. Witness word1L,2U,S,3L,4U,S/maxima1,1,1,1/children2,5. Certifies that all positive point activity, even with all sibling maxima minimal and globals legal, gives no full-bound positivity witness. This is a lower-shortcut obstruction, not an interleaved maximal-segment exchange counterexample.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_all_unit_sibling_and_point_capacity_zero_counterexample : ∃ σ : Ctx.Context,
  σ.WellFormed ∧ σ.a = 4 ∧ σ.u = 4 ∧ σ.k = 4 ∧
  σ.maxima = [1, 1, 1, 1] ∧ σ.childPositions = [2, 5] ∧
  2 ≤ σ.numRuns ∧ σ.bound = 0 ∧
  ∀ p ∈ σ.childPositions, σ.cupLimit p p = 1 ∧ σ.capLimit p p = 1 := by
  let σ : Ctx.Context :=
    { a := 4, u := 4, k := 4,
      word := [.ext 1 .lower, .ext 2 .upper, .child,
        .ext 3 .lower, .ext 4 .upper, .child],
      maxima := [1, 1, 1, 1] }
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p j v hp
      have hplen : p < 6 := by
        by_contra h
        have hletter := Ctx.Context.letterAt_of_length_le σ
          (show σ.word.length ≤ p by change 6 ≤ p; omega)
        rw [hletter] at hp
        cases hp
      have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 2 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 3 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.ext 4 .upper = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
  refine ⟨σ, hwf, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  intro p hp
  have hpCases : p = 2 ∨ p = 5 := by
    change p ∈ [2, 5] at hp
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hp
  rcases hpCases with rfl | rfl <;> exact ⟨by decide, by decide⟩

end ErdosSzekeres
