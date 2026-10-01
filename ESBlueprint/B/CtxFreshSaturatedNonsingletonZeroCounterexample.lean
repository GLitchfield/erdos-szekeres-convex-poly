import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A well-formed 4/4/4 context with no indexed history on the fresh upper axis and positive opposite source point capacity has a two-child upper(k-2) part with full bound zero, although both kept point capacities are exactly one. Witness word1L,S,1L,S,1L,S,1L, maxima1, keep1,3, omitted5. Certifies that the singleton hypothesis of the clear-fresh-axis exact-one theorem cannot be dropped; positive point activity does not supply a nonsingleton full-bound lower witness.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_fresh_saturated_nonsingleton_zero_counterexample : ∃ σ : Ctx.Context, σ.WellFormed ∧ σ.a = 4 ∧ σ.u = 4 ∧ σ.k = 4 ∧ σ.levelsOn .upper 0 = [] ∧ σ.childPositions = [1, 3, 5] ∧ 0 < σ.cupLimit 1 1 ∧ (σ.part [1, 3] .upper 2).childPositions = [1, 3] ∧ 2 ≤ (σ.part [1, 3] .upper 2).numRuns ∧ (σ.part [1, 3] .upper 2).bound = 0 ∧ ∀ p ∈ (σ.part [1, 3] .upper 2).childPositions, (σ.part [1, 3] .upper 2).cupLimit p p = 1 ∧ (σ.part [1, 3] .upper 2).capLimit p p = 1 := by
  let σ : Ctx.Context :=
    { a := 4, u := 4, k := 4,
      word := [.ext 1 .lower, .child, .ext 1 .lower, .child,
        .ext 1 .lower, .child, .ext 1 .lower],
      maxima := [1] }
  have hwf : σ.WellFormed := by
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
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
  refine ⟨σ, hwf, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  intro p hp
  have hpCases : p = 1 ∨ p = 3 := by
    change p ∈ [1, 3] at hp
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hp
  rcases hpCases with rfl | rfl <;> exact ⟨by decide, by decide⟩

end ErdosSzekeres
