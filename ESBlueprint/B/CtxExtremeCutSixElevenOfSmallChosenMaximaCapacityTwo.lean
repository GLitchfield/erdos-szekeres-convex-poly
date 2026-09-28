import ESBlueprint.B.CtxExtremeNextCutOfSmallChosenMaximaCapacityTwo

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- At k six, an extreme chosen new maximum, uniformly unit old chosen maxima, and chosen capacity at most two at every active companion child give the exact cut bound eleven. The extreme part costs one and the checked small-maxima linear companion costs at most ten. Arbitrary kept lists, opposite new maxima, inactive children, and independent fuels remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_positive_letters, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_small_maxima_active_capacity_two_linear_potential
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hchosen : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hoppositeLower : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hmax : ∀ j ∈ σ.levelsOn s 0, σ.maximumAt j ≤ 1) (keep : List ℕ) (m n p : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hm : m + 2 = σ.k) (hk : σ.k = 6) : let A := σ.part keep s m; let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; (∀ q ∈ B.childPositions, 0 < B.cupLimit q q → 0 < B.capLimit q q → (match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q) ≤ 2) → (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 11) ∧ A.bound + B.bound ≤ 11 := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
    | Ctx.Side.lower => ρ.u
    | Ctx.Side.upper => ρ.a
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change
    (∀ q ∈ B.childPositions, 0 < B.cupLimit q q → 0 < B.capLimit q q →
      (match s with
        | Ctx.Side.lower => B.cupLimit q q
        | Ctx.Side.upper => B.capLimit q q) ≤ 2) →
    (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 11) ∧
    A.bound + B.bound ≤ 11
  intro hsmall
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
  have hPosB := ctx_part_positive_letters σ rest t n
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter, decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hBMax : ∀ j ∈ B.levelsOn s 0, B.maximumAt j ≤ B.k - 5 := by
    intro j hj
    have hjLevel : j ∈ B.levels := (List.mem_filter.mp hj).1
    have hjs : B.sideAt j = s :=
      (of_decide_eq_true (List.mem_filter.mp hj).2).1
    change j ∈ (σ.part rest t n).levels at hjLevel
    rw [Ctx.Context.part_levels] at hjLevel
    rcases List.mem_cons.mp hjLevel with hjOne | hjOld
    · subst j
      exact False.elim (hne (hjs.symm.trans hBsideOne))
    · obtain ⟨R, hR, hRj⟩ := List.mem_map.mp hjOld
      have hRpos : 1 ≤ R := Ctx.Context.one_le_of_mem_levels hR
      have hBsideR : B.sideAt (R + 1) = σ.sideAt R :=
        Ctx.Context.part_sideAt_succ σ rest t n hRpos
      have hjsR : B.sideAt (R + 1) = s := by
        rw [hRj]
        exact hjs
      have hRs : σ.sideAt R = s := hBsideR.symm.trans hjsR
      have hROn : R ∈ σ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hR, by simp [hRs]⟩
      have hRmax := hmax R hROn
      calc
        B.maximumAt j = σ.maximumAt R := by
          rw [← hRj]
          exact Ctx.Context.part_maximumAt_succ σ rest t n hRpos
        _ ≤ 1 := hRmax
        _ ≤ σ.k - 5 := by rw [hk]
        _ = B.k - 5 := by rfl
  have hBChosen : G B s ≤ 5 := by
    cases s <;> exact hchosen
  have hBOppositeLower : 2 ≤ G B t := by
    cases t <;> exact hoppositeLower
  have hBWidth : 1 ≤ G B t - 1 := by omega
  have hPotential := ctx_small_maxima_active_capacity_two_linear_potential B hPosB
    s t hne hBChosen (by change 5 ≤ σ.k; omega) hBMax hsmall hBWidth
  have hBOpposite : G B t ≤ 5 := by
    cases t <;> exact hopposite
  have hWidthUpper : G B t - 1 ≤ 4 := by omega
  have hLinear : 3 * (G B t - 1) - 2 ≤ 10 := by omega
  have hBFuel (fuel : ℕ) : Ctx.Context.boundFuel fuel B ≤ 10 :=
    (hPotential.1 fuel).trans hLinear
  have hBBound : B.bound ≤ 10 := hPotential.2.trans hLinear
  exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hBFuel g)).trans (by omega),
    (Nat.add_le_add hA.2 hBBound).trans (by omega)⟩

end ErdosSzekeres
