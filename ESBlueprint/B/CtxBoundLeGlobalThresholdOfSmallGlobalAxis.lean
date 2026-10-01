import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every fuel approximation and the full raw context bound are at most the exact decomposable threshold when legal positive globals have either axis at most three. Arbitrary indexed histories, maxima, inactive children and positive unindexed barriers are allowed; no well-formedness, empty-history, run-pattern, boundary-marker or recursive premise. Packages closed zero-global, common-singleton-rank and rank-region potentials into exact small-global threshold upper edges for the R16 marked-root normalization route.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_bound_le_global_threshold_of_small_global_axis (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (ha : 1 ≤ σ.a) (hu : 1 ≤ σ.u) (hak : σ.a ≤ σ.k) (huk : σ.u ≤ σ.k) (hsmall : σ.a ≤ 3 ∨ σ.u ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ decomposableThreshold σ.a σ.u σ.k) ∧ σ.bound ≤ decomposableThreshold σ.a σ.u σ.k := by
  classical
  by_cases ha1 : σ.a ≤ 1
  · have hz := ctx_bound_zero_of_unit_global_axis σ (Or.inl ha1)
    have ht : decomposableThreshold σ.a σ.u σ.k = 0 := by
      rw [show σ.a = 1 by omega]
      simp
    rw [ht]
    exact ⟨fun fuel => (hz.1 fuel).le,hz.2.le⟩
  by_cases hu1 : σ.u ≤ 1
  · have hz := ctx_bound_zero_of_unit_global_axis σ (Or.inr hu1)
    have ht : decomposableThreshold σ.a σ.u σ.k = 0 := by
      rw [show σ.u = 1 by omega]
      simp
    rw [ht]
    exact ⟨fun fuel => (hz.1 fuel).le,hz.2.le⟩
  have ha2 : 2 ≤ σ.a := by omega
  have hu2 : 2 ≤ σ.u := by omega
  rcases hsmall with hsmall | hsmall
  · by_cases haeq : σ.a = 2
    · have hrank : ∀ p ∈ σ.childPositions,
          0 < σ.cupLimit p p → 0 < σ.capLimit p p →
          σ.leftExt Side.upper 0 p + 1 = 1 ∧
          1 + σ.rightExt Side.upper 0 p = σ.a-1 := by
        intro p hp hcup hcap
        unfold capLimit chainExt at hcap
        rw [haeq] at hcap ⊢
        constructor <;> omega
      have hb := ctx_bound_le_one_of_common_singleton_rank σ hpositive Side.upper 1 hrank
      have ht : decomposableThreshold σ.a σ.u σ.k = 1 := by
        rw [haeq,decomposableThreshold_eq_choose (by omega) hu2 (by omega)]
        simp
      rw [ht]
      exact ⟨hb.1,hb.2.1⟩
    · have haeq : σ.a = 3 := by omega
      have hb := ctx_small_global_axis_rank_region_potential σ hpositive
        Side.upper Side.lower (by decide) (by change σ.a ≤ 3; omega)
      have ht : decomposableThreshold σ.a σ.u σ.k = σ.u-1 := by
        rw [haeq,decomposableThreshold_eq_choose (by omega) hu2 (by omega)]
        have hrow : 3+σ.u-4 = σ.u-1 := by omega
        rw [hrow]
        simp
      rw [ht]
      exact ⟨fun fuel => (hb.1 fuel).trans hb.2.2.1,hb.2.1.trans hb.2.2.1⟩
  · by_cases hueq : σ.u = 2
    · have hrank : ∀ p ∈ σ.childPositions,
          0 < σ.cupLimit p p → 0 < σ.capLimit p p →
          σ.leftExt Side.lower 0 p + 1 = 1 ∧
          1 + σ.rightExt Side.lower 0 p = σ.u-1 := by
        intro p hp hcup hcap
        unfold cupLimit chainExt at hcup
        rw [hueq] at hcup ⊢
        constructor <;> omega
      have hb := ctx_bound_le_one_of_common_singleton_rank σ hpositive Side.lower 1 hrank
      have ht : decomposableThreshold σ.a σ.u σ.k = 1 := by
        rw [hueq,decomposableThreshold_eq_choose ha2 (by omega) (by omega)]
        have hrow : σ.a+2-4 = σ.a-2 := by omega
        rw [hrow,Nat.choose_self]
      rw [ht]
      exact ⟨hb.1,hb.2.1⟩
    · have hueq : σ.u = 3 := by omega
      have hb := ctx_small_global_axis_rank_region_potential σ hpositive
        Side.lower Side.upper (by decide) (by change σ.u ≤ 3; omega)
      have ht : decomposableThreshold σ.a σ.u σ.k = σ.a-1 := by
        rw [hueq,decomposableThreshold_eq_choose ha2 (by omega) (by omega)]
        have hrow : σ.a+3-4 = σ.a-1 := by omega
        rw [hrow,Nat.choose_symm_of_eq_add (show σ.a-1 = (σ.a-2)+1 by omega),
          Nat.choose_one_right]
      rw [ht]
      exact ⟨fun fuel => (hb.1 fuel).trans hb.2.2.1,hb.2.1.trans hb.2.2.1⟩

end ErdosSzekeres
