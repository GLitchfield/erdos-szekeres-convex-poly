import ESBlueprint.B.CtxNonmonotoneNewMarkerCutBoundExceptSixExtreme
import ESBlueprint.B.CtxSmallGlobalAxisSaturatedTriangleBound

namespace ErdosSzekeres

set_option maxHeartbeats 4000000 in
/-- For an extreme chosen new maximum m=k-2, any original chosen-axis sibling maximum at least k-4 forces the complementary part into global at most four after checked upper normalization. The extreme part costs at most one and the normalized companion satisfies the checked saturated triangle estimate, whose sum fits the next quadratic budget for k at least six. Positive labels, distinct axes, source opposite global at most k, arbitrary kept list, arbitrary opposite new maximum and every fuel approximation are explicit. No retained/removed witness, maximum coupling, marker occurrence, history-depth, nonmonotone geometry or recursive-potential premise is needed. This covers the k=6,m=4,n=1 next-band obstruction whenever some chosen-history maximum is at least two, leaving only the documented all-unit chosen-history case. Exact searches in runs/sol-12h/search-extreme-large-history.json, search-large-maximum-normalized-companion.json and search-extreme-part-companion.json found only a stricter straddling theorem and no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_positive_letters, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_small_global_axis_saturated_triangle_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_next_cut_of_large_chosen_history_maximum (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k) (hk : 6 ≤ σ.k) (R : ℕ) (hR : R ∈ σ.levels) (hRs : σ.sideAt R = s) (hmaximum : σ.k - 4 ≤ σ.maximumAt R) (keep : List ℕ) (m n : ℕ) (hm : m + 2 = σ.k) : let A := σ.part keep s m; let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ (σ.k - 2)^2 - (σ.k - 2) + 1) ∧ A.bound + B.bound ≤ (σ.k - 2)^2 - (σ.k - 2) + 1 := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
    | Ctx.Side.lower => ρ.u
    | Ctx.Side.upper => ρ.a
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change
    (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤
      (σ.k - 2) ^ 2 - (σ.k - 2) + 1) ∧
    A.bound + B.bound ≤ (σ.k - 2) ^ 2 - (σ.k - 2) + 1
  have hPosA := ctx_part_positive_letters σ keep s m
  have hAlevel : 1 ∈ A.levels := by
    simp [A, Ctx.Context.part_levels]
  have hAmaximum : A.maximumAt 1 = m := by
    exact Ctx.Context.part_maximumAt_one σ keep s m
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
  have hBside : B.sideAt (R + 1) = s := by
    exact (Ctx.Context.part_sideAt_succ σ rest t n hRpos).trans hRs
  have hBmaximum : B.maximumAt (R + 1) = σ.maximumAt R := by
    exact Ctx.Context.part_maximumAt_succ σ rest t n hRpos
  let τ : Ctx.Context := match B.sideAt (R + 1) with
    | Ctx.Side.lower => {B with u := min B.u (B.k - B.maximumAt (R + 1)), maxima := B.maxima.take R}
    | Ctx.Side.upper => {B with a := min B.a (B.k - B.maximumAt (R + 1)), maxima := B.maxima.take R}
  have hτWord : τ.word = B.word := by
    cases hs : B.sideAt (R + 1) <;> simp only [τ, hs]
  have hτLetter (p : ℕ) : τ.letterAt p = B.letterAt p := by
    simp only [Ctx.Context.letterAt, hτWord]
  have hPosτ : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hτLetter] at hp
    exact hPosB p j v hp
  have hBK : B.k = σ.k := by rfl
  have hτK : τ.k = σ.k := by
    cases hs : B.sideAt (R + 1) <;> simpa only [τ, hs] using hBK
  have hτChosen : G τ s ≤ 4 := by
    cases s <;> simp only [G, τ, hBside]
    all_goals
      exact (Nat.min_le_right _ _).trans (show B.k - B.maximumAt (R + 1) ≤ 4 by
        rw [hBK, hBmaximum]
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
    rw [hτOpp, hτK]
    cases t <;> exact hopposite
  have hnorm := ctx_sibling_maximum_upper_normalize B (R + 1) hBlevel
  have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel B ≤
      Ctx.Context.boundFuel fuel τ := by
    simpa only [τ, Nat.add_sub_cancel] using hnorm.2.1
  have hBoundNorm : B.bound ≤ τ.bound := by
    simpa only [τ, Nat.add_sub_cancel] using hnorm.2.2
  have hTriangle := ctx_small_global_axis_saturated_triangle_bound τ hPosτ s t hne
    hτChosen hτOpposite (by rw [hτK]; omega)
  have hBFuel (fuel : ℕ) : Ctx.Context.boundFuel fuel B ≤
      (σ.k - 2).choose 2 + (σ.k - 1) := by
    exact (hFuelNorm fuel).trans (by simpa only [hτK] using hTriangle.1 fuel)
  have hBBound : B.bound ≤ (σ.k - 2).choose 2 + (σ.k - 1) := by
    exact hBoundNorm.trans (by simpa only [hτK] using hTriangle.2.1)
  have hTwoChoose (r : ℕ) : 2 * (r + 1).choose 2 = r * r + r := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  have hNumeric (k : ℕ) (hk6 : 6 ≤ k) :
      1 + ((k - 2).choose 2 + (k - 1)) ≤ (k - 2) ^ 2 - (k - 2) + 1 := by
    let z := k - 6
    have hz : 0 ≤ z := Nat.zero_le z
    have h2 : k - 2 = z + 4 := by
      dsimp [z]
      omega
    have h1 : k - 1 = z + 5 := by
      dsimp [z]
      omega
    rw [h2, h1]
    have hc := hTwoChoose (z + 3)
    have hs : z + 4 ≤ (z + 4) ^ 2 := by
      nlinarith
    have hcancel := Nat.sub_add_cancel hs
    set_option maxHeartbeats 2000000 in
      nlinarith only [hz, hc, hcancel]
  constructor
  · intro f g
    exact (Nat.add_le_add (hA.1 f) (hBFuel g)).trans (hNumeric σ.k hk)
  · exact (Nat.add_le_add hA.2 hBBound).trans (hNumeric σ.k hk)


end ErdosSzekeres
