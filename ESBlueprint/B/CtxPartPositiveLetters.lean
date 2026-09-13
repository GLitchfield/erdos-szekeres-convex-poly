import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Every external letter in a part has positive level, without an assumption on the original context. Extracts the repeated hPartPositive argument used by context cut bounds.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_actual_marker_quadratic_penultimate_cut_bound -/
theorem ctx_part_positive_letters (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side) (m : ℕ) : ∀ x j w, (ρ.part keep v m).letterAt x = Ctx.Letter.ext j w → 1 ≤ j := by
  intro x j w hx
  have hxlen : x < ρ.word.length := by
    by_contra hge
    rw [Ctx.Context.letterAt_of_length_le _ (by
      rw [Ctx.Context.part_word_length]
      omega)] at hx
    cases hx
  rcases hρ : ρ.letterAt x with _ | ⟨l, s⟩
  · rw [Ctx.Context.part_letterAt_of_child ρ keep v m hxlen hρ] at hx
    by_cases hk : x ∈ keep
    · simp [hk] at hx
    · simp only [hk, if_false, Ctx.Letter.ext.injEq] at hx
      omega
  · rw [Ctx.Context.part_letterAt_of_ext ρ keep v m hxlen hρ] at hx
    simp only [Ctx.Letter.ext.injEq] at hx
    omega


end ErdosSzekeres
