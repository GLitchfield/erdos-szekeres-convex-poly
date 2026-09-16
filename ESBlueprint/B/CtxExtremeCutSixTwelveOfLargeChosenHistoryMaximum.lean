import ESBlueprint.B.CtxExtremeNextCutOfLargeChosenHistoryMaximum

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- At k six, an extreme chosen new maximum m=k-2 and any original chosen-axis maximum at least two give a cut sum at most twelve. The extreme chosen part costs at most one; normalizing the complementary part at the old maximum reduces the chosen global to four, and the saturated triangle bound costs at most eleven. Arbitrary kept lists, opposite new maxima, inactive children, and independent fuels remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_positive_letters, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_small_global_axis_saturated_triangle_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_twelve_of_large_chosen_history_maximum (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (R : ℕ) (hR : R ∈ σ.levels) (hRs : σ.sideAt R = s) (hmaximum : 2 ≤ σ.maximumAt R) (keep : List ℕ) (m n : ℕ) (hm : m + 2 = σ.k) (hk : σ.k = 6) : let A := σ.part keep s m; let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧ A.bound + B.bound ≤ 12 := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
    | Ctx.Side.lower => ρ.u
    | Ctx.Side.upper => ρ.a
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
    A.bound + B.bound ≤ 12
  have hPosA := ctx_part_positive_letters σ keep s m
  have hAlevel : 1 ∈ A.levels := by
    simp [A, Ctx.Context.part_levels]
  have hAmaximum : A.maximumAt 1 = m :=
    Ctx.Context.part_maximumAt_one σ keep s m
  have hAlarge : A.k - 2 ≤ A.maximumAt 1 := by
    rw [hAmaximum]
    change σ.k - 2 ≤ m
    omega
  have hA := ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAlevel hAlarge
  have hRpos : 1 ≤ R := Ctx.Context.one_le_of_mem_levels hR
  have hPosB := ctx_part_positive_letters σ rest t n
  have hBlevel : R + 1 ∈ B.levels := by
    change R + 1 ∈ (σ.part rest t n).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨R, hR, rfl⟩)
  have hBside : B.sideAt (R + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hRpos).trans hRs
  have hBmaximum : B.maximumAt (R + 1) = σ.maximumAt R :=
    Ctx.Context.part_maximumAt_succ σ rest t n hRpos
  let τ : Ctx.Context := match B.sideAt (R + 1) with
    | Ctx.Side.lower =>
        {B with u := min B.u (B.k - B.maximumAt (R + 1)), maxima := B.maxima.take R}
    | Ctx.Side.upper =>
        {B with a := min B.a (B.k - B.maximumAt (R + 1)), maxima := B.maxima.take R}
  have hτWord : τ.word = B.word := by
    cases hs : B.sideAt (R + 1) <;> simp only [τ, hs]
  have hτLetter (p : ℕ) : τ.letterAt p = B.letterAt p := by
    simp only [Ctx.Context.letterAt, hτWord]
  have hPosτ : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hτLetter] at hp
    exact hPosB p j v hp
  have hBK : B.k = σ.k := rfl
  have hτK : τ.k = σ.k := by
    cases hs : B.sideAt (R + 1) <;> simpa only [τ, hs] using hBK
  have hτChosen : G τ s ≤ 4 := by
    cases s <;> simp only [G, τ, hBside]
    all_goals
      exact (Nat.min_le_right _ _).trans (show B.k - B.maximumAt (R + 1) ≤ 4 by
        rw [hBK, hBmaximum, hk]
        omega)
  have hτOpp : G τ t = G σ t := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, τ, hBside]
      rfl
    · simp only [G, τ, hBside]
      rfl
    · exact False.elim (hne rfl)
  have hτOpposite : G τ t ≤ τ.k := by
    rw [hτOpp, hτK, hk]
    cases t <;> simp only [G] at hopposite ⊢ <;> omega
  have hnorm := ctx_sibling_maximum_upper_normalize B (R + 1) hBlevel
  have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel B ≤
      Ctx.Context.boundFuel fuel τ := by
    simpa only [τ, Nat.add_sub_cancel] using hnorm.2.1
  have hBoundNorm : B.bound ≤ τ.bound := by
    simpa only [τ, Nat.add_sub_cancel] using hnorm.2.2
  have hTriangle := ctx_small_global_axis_saturated_triangle_bound τ hPosτ s t hne
    hτChosen hτOpposite (by rw [hτK, hk]; omega)
  have hBFuel (fuel : ℕ) : Ctx.Context.boundFuel fuel B ≤ 11 := by
    have hh := (hFuelNorm fuel).trans (hTriangle.1 fuel)
    rw [hτK, hk] at hh
    norm_num at hh ⊢
    exact hh
  have hBBound : B.bound ≤ 11 := by
    have hh := hBoundNorm.trans hTriangle.2.1
    rw [hτK, hk] at hh
    norm_num at hh ⊢
    exact hh
  exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hBFuel g)).trans (by omega),
    (Nat.add_le_add hA.2 hBBound).trans (by omega)⟩

end ErdosSzekeres
