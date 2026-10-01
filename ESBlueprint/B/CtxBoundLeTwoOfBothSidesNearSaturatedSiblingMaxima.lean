import ESBlueprint.B.CtxBoundLeOppositeWidthOfSiblingMaximumGeKMinusThree

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Indexed sibling maxima at least k-3 on both axes bound every fuel approximation and the full recursive context by two. Normalize the older selected level to cap its global parameter at three while retaining the younger indexed level and maximum; the closed younger-side opposite-width estimate then gives three minus one. Positive actual external labels suffice for arbitrary raw histories, unused indexed levels, globals, inactive children and child patterns, without well-formedness, run-count or length hypotheses. Reusable for opposite-axis proper parts and the k=4 boundary.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (L U : ℕ) (hL : L ∈ σ.levelsOn Ctx.Side.lower 0)
  (hU : U ∈ σ.levelsOn Ctx.Side.upper 0)
  (hLmaximum : σ.k - 3 ≤ σ.maximumAt L)
  (hUmaximum : σ.k - 3 ≤ σ.maximumAt U) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2) ∧ σ.bound ≤ 2 := by
  classical
  have hOrdered (s t : Ctx.Side) (hne : s ≠ t) (N M : ℕ)
      (hN : N ∈ σ.levelsOn s 0) (hM : M ∈ σ.levelsOn t 0)
      (hNM : N < M)
      (hNmaximum : σ.k - 3 ≤ σ.maximumAt N)
      (hMmaximum : σ.k - 3 ≤ σ.maximumAt M) :
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2) ∧ σ.bound ≤ 2 := by
    have hNmem : N ∈ σ.levels := (List.mem_filter.mp hN).1
    have hMmem : M ∈ σ.levels := (List.mem_filter.mp hM).1
    have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hN).1
    have hNs : σ.sideAt N = s := by simpa using (List.mem_filter.mp hN).2
    have hMs : σ.sideAt M = t := by simpa using (List.mem_filter.mp hM).2
    let τ : Ctx.Context := match σ.sideAt M with
      | .lower =>
          { σ with u := min σ.u (σ.k - σ.maximumAt M), maxima := σ.maxima.take (M - 1) }
      | .upper =>
          { σ with a := min σ.a (σ.k - σ.maximumAt M), maxima := σ.maxima.take (M - 1) }
    have hτWord : τ.word = σ.word := by
      cases hs : σ.sideAt M <;> simp only [τ, hs]
    have hτMaxima : τ.maxima = σ.maxima.take (M - 1) := by
      cases hs : σ.sideAt M <;> simp only [τ, hs]
    have hτK : τ.k = σ.k := by
      cases hs : σ.sideAt M <;> simp only [τ, hs]
    have hτLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
      simp only [Ctx.Context.letterAt, hτWord]
    have hτExt (j : ℕ) : τ.extPositions j = σ.extPositions j := by
      simp only [Ctx.Context.extPositions, hτWord, hτLetter]
    have hτSide (j : ℕ) : τ.sideAt j = σ.sideAt j := by
      simp only [Ctx.Context.sideAt, hτExt, hτLetter]
    have hτPositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      rw [hτLetter] at hp
      exact hpositive p j v hp
    have hNlength : N ≤ σ.maxima.length := by
      simp only [Ctx.Context.levels, List.mem_map, List.mem_range] at hNmem
      obtain ⟨i, hi, he⟩ := hNmem
      omega
    have hτNlength : N ≤ τ.maxima.length := by
      rw [hτMaxima, List.length_take]
      omega
    have hτN : N ∈ τ.levels := by
      simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
      exact ⟨N - 1, by omega, by omega⟩
    have hτNs : τ.sideAt N = s := (hτSide N).trans hNs
    have hτMaximum : τ.maximumAt N = σ.maximumAt N := by
      simp only [Ctx.Context.maximumAt, hτMaxima,
        List.getElem?_take_of_lt (by omega : N - 1 < M - 1)]
    have hτMaximumNear : τ.k - 3 ≤ τ.maximumAt N := by
      rw [hτK, hτMaximum]
      exact hNmaximum
    have hτSmall : (match t with | .lower => τ.u | .upper => τ.a) ≤ 3 := by
      cases t <;> simp only [τ, hMs]
      all_goals
        exact (Nat.min_le_right _ _).trans (by omega)
    have hWidth : (match t with | .lower => τ.u | .upper => τ.a) - 1 ≤ 2 := by
      omega
    have hnorm := ctx_sibling_maximum_upper_normalize σ M hMmem
    have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel σ ≤
        Ctx.Context.boundFuel fuel τ := by
      simpa only [τ] using hnorm.2.1
    have hBoundNorm : σ.bound ≤ τ.bound := by
      simpa only [τ] using hnorm.2.2
    have hwidth := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
      τ hτPositive s t hne N hτN hτNs hτMaximumNear
    cases t <;> exact ⟨fun fuel => (hFuelNorm fuel).trans ((hwidth.1 fuel).trans hWidth),
      hBoundNorm.trans (hwidth.2.trans hWidth)⟩
  have hLside : σ.sideAt L = Ctx.Side.lower := by
    simpa using (List.mem_filter.mp hL).2
  have hUside : σ.sideAt U = Ctx.Side.upper := by
    simpa using (List.mem_filter.mp hU).2
  have hLU : L ≠ U := by
    intro h
    rw [h, hUside] at hLside
    cases hLside
  by_cases horder : L < U
  · exact hOrdered .lower .upper (by decide) L U hL hU horder hLmaximum hUmaximum
  · exact hOrdered .upper .lower (by decide) U L hU hL (by omega) hUmaximum hLmaximum

end ErdosSzekeres
