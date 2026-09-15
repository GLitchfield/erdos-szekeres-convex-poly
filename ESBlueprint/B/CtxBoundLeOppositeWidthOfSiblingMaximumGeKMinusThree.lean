import ESBlueprint.B.CtxExtremeNextCutOfLargeChosenHistoryMaximum

namespace ErdosSzekeres

/-- If an indexed sibling maximum on the chosen side is at least k-3, checked upper normalization lowers that side to global width at most three; the exact small-global rank/region potential then bounds every fuel approximation and the full recursive bound by the opposite width minus one. Positive labels and distinct axes are explicit, while all other histories, maxima and child patterns remain arbitrary. This is the reusable m=3 endpoint-cut estimate for the exact k=6 obstruction. Exact search found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_small_global_axis_rank_region_potential
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hmaximum : σ.k - 3 ≤ σ.maximumAt N) : (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) ∧ σ.bound ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
    | Ctx.Side.lower => ρ.u
    | Ctx.Side.upper => ρ.a
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower =>
        { σ with u := min σ.u (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    | Ctx.Side.upper =>
        { σ with a := min σ.a (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
  have hτWord : τ.word = σ.word := by
    cases hs : σ.sideAt N <;> simp only [τ, hs]
  have hτLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
    simp only [Ctx.Context.letterAt, hτWord]
  have hτPositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hτLetter] at hp
    exact hpositive p j v hp
  have hτSmall : G τ s ≤ 3 := by
    cases s <;> simp only [G, τ, hNs]
    all_goals
      exact (Nat.min_le_right _ _).trans (by omega)
  have hτOpposite : G τ t = G σ t := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, τ, hNs]
    · simp only [G, τ, hNs]
    · exact False.elim (hne rfl)
  have hnorm := ctx_sibling_maximum_upper_normalize σ N hN
  have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      Ctx.Context.boundFuel fuel τ := by
    simpa only [τ] using hnorm.2.1
  have hBoundNorm : σ.bound ≤ τ.bound := by
    simpa only [τ] using hnorm.2.2
  have hpotential := ctx_small_global_axis_rank_region_potential
    τ hτPositive s t hne hτSmall
  have hτFuel : ∀ fuel, Ctx.Context.boundFuel fuel τ ≤ G τ t - 1 := by
    intro fuel
    cases t <;> simpa only [G] using
      (hpotential.1 fuel).trans hpotential.2.2.1
  have hτBound : τ.bound ≤ G τ t - 1 := by
    cases t <;> simpa only [G] using
      hpotential.2.1.trans hpotential.2.2.1
  have hFuelFinal : ∀ fuel, Ctx.Context.boundFuel fuel σ ≤ G σ t - 1 := by
    intro fuel
    rw [← hτOpposite]
    exact (hFuelNorm fuel).trans (hτFuel fuel)
  have hBoundFinal : σ.bound ≤ G σ t - 1 := by
    rw [← hτOpposite]
    exact hBoundNorm.trans hτBound
  cases s <;> cases t
  · exact False.elim (hne rfl)
  · exact ⟨hFuelFinal, hBoundFinal⟩
  · exact ⟨hFuelFinal, hBoundFinal⟩
  · exact False.elim (hne rfl)

end ErdosSzekeres
