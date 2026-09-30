import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every recursive fuel approximation and the full context bound vanish when either global cap or cup parameter is at most one. Valid for arbitrary raw words, maxima and k, without well-formedness. Parts retain the zero global axis, and the defining recurrence sums zero bounds. Removes the a=1 or u=1 boundary in the one-level-root contraction C1r, whose hypotheses allow values outside Context.WellFormed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_zero_of_unit_global_axis (σ : Ctx.Context) (hzero : σ.a ≤ 1 ∨ σ.u ≤ 1) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
  classical
  have hBase : ∀ (ρ : Context), ρ.a ≤ 1 ∨ ρ.u ≤ 1 → ρ.base = 0 := by
    intro ρ hρ
    cases hp : ρ.childPositions.head? with
    | none => simp [base, hp]
    | some p =>
      rcases hρ with ha | hu
      · have hz : ρ.a - 1 = 0 := by omega
        simp [base, hp, capLimit, hz]
      · have hz : ρ.u - 1 = 0 := by omega
        simp [base, hp, cupLimit, hz]
  have hFuel : ∀ fuel (ρ : Context), ρ.a ≤ 1 ∨ ρ.u ≤ 1 → boundFuel fuel ρ = 0 := by
    intro fuel
    induction fuel with
    | zero => intro ρ _; rfl
    | succ fuel ih =>
      intro ρ hρ
      rw [boundFuel.eq_2]
      by_cases hr : ρ.numRuns ≤ 1
      · rw [if_pos hr]
        exact hBase ρ hρ
      · rw [if_neg hr]
        apply Nat.eq_zero_of_le_zero
        apply getD_max?_le
        intro value hv
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨block, _, d, _, hv⟩ := hv
        rcases hv with rfl | rfl
        · rw [ih (ρ.part block Side.lower (d + 1)) hρ,
            ih (ρ.part (ρ.childPositions.filter (· ∉ block)) Side.upper
              (ρ.k - 1 - (d + 1))) hρ]
        · rw [ih (ρ.part block Side.upper (ρ.k - 1 - (d + 1))) hρ,
            ih (ρ.part (ρ.childPositions.filter (· ∉ block)) Side.lower (d + 1)) hρ]
  exact ⟨fun fuel => hFuel fuel σ hzero, hFuel _ σ hzero⟩


end ErdosSzekeres
