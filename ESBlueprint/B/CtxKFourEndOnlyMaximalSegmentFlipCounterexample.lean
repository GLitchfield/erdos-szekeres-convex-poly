import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A well-formed k=4 interleaved five-child partition has value two, but both endpoint maximal-segment flips have every legal orientation/coupling value at most one. Witness 4/3/4 word S,1L,S,S,S,1L,S and maxima1, keep0,3,6. Certifies the strict end-only exchange obstruction; does not refute any-length maximal-segment exchange, whose interior flips work on this witness.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_k_four_end_only_maximal_segment_flip_counterexample : ∃ σ : Ctx.Context, σ.WellFormed ∧ σ.k = 4 ∧ σ.childPositions = [0, 2, 3, 4, 6] ∧ 2 ≤ σ.numRuns ∧ [0, 3, 6] ∉ σ.blocks ∧ [2, 4] ∉ σ.blocks ∧ (σ.part [0, 3, 6] .upper 1).bound + (σ.part [2, 4] .lower 2).bound = 2 ∧ ∀ d, 1 ≤ d → d ≤ σ.k - 2 → (σ.part [3, 6] .lower d).bound + (σ.part [0, 2, 4] .upper (σ.k - 1 - d)).bound ≤ 1 ∧ (σ.part [3, 6] .upper (σ.k - 1 - d)).bound + (σ.part [0, 2, 4] .lower d).bound ≤ 1 ∧ (σ.part [0, 3] .lower d).bound + (σ.part [2, 4, 6] .upper (σ.k - 1 - d)).bound ≤ 1 ∧ (σ.part [0, 3] .upper (σ.k - 1 - d)).bound + (σ.part [2, 4, 6] .lower d).bound ≤ 1 := by
  let σ : Ctx.Context :=
    { a := 4, u := 3, k := 4,
      word := [.child, .ext 1 .lower, .child, .child, .child,
        .ext 1 .lower, .child],
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
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
      · change Ctx.Letter.ext 1 .lower = Ctx.Letter.ext j v at hp
        cases hp
        decide
      · change Ctx.Letter.child = Ctx.Letter.ext j v at hp
        cases hp
  refine ⟨σ, hwf, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · decide
  · intro d hd hdk
    have hdCases : d = 1 ∨ d = 2 := by change d ≤ 4 - 2 at hdk; omega
    rcases hdCases with rfl | rfl
    · exact ⟨by decide, by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide, by decide⟩

end ErdosSzekeres
