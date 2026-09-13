import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Both endpoint extensions at any history cutoff are bounded by their zero-cutoff values. Extracts repeated cutoff inclusion and maximum monotonicity proofs used by saturated context bounds.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_small_maxima_active_capacity_two_linear_potential -/
theorem ctx_extensions_le_zero_cutoff (ρ : Ctx.Context) (v : Ctx.Side) (top z : ℕ) : ρ.leftExt v top z ≤ ρ.leftExt v 0 z ∧ ρ.rightExt v top z ≤ ρ.rightExt v 0 z := by
  have hlevels : (ρ.levelsOn v top).Sublist (ρ.levelsOn v 0) := by
    unfold Ctx.Context.levelsOn
    apply List.monotone_filter_right
    intro l hl
    simp only [decide_eq_true_eq] at hl ⊢
    exact ⟨hl.1, Or.inl (by simpa using rfl)⟩
  have hmono (step : ℕ × ℕ → ℕ → ℕ × ℕ) :
      (((ρ.levelsOn v top).sublists.map fun ls => (ls.foldl step (z, 0)).2).max?).getD 0 ≤
        (((ρ.levelsOn v 0).sublists.map fun ls => (ls.foldl step (z, 0)).2).max?).getD 0 := by
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.1 hx
    refine ⟨_, List.mem_map.2 ⟨ls, ?_, rfl⟩, le_rfl⟩
    exact List.mem_sublists.2 ((List.mem_sublists.1 hls).trans hlevels)
  constructor
  · unfold Ctx.Context.leftExt
    exact hmono _
  · unfold Ctx.Context.rightExt
    exact hmono _


end ErdosSzekeres
