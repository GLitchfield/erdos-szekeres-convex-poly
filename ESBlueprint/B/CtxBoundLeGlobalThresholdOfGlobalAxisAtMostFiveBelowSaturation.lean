import ESBlueprint.B.CtxSmallGlobalAxisSaturatedTriangleBound
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every fuel approximation and full bound of an arbitrary positive-label raw context with legal globals one through k, either global at most five, and a+u at most k+3 are at most the exact decomposable threshold. Arbitrary indexed history, sibling maxima, child/run patterns and positive unindexed barriers. Reuse the checked axis-at-most-four upper; when the small axis is exactly five, the closed cubic rank potential choose(other global+1,3) equals the classical threshold under the explicit below-saturation hypothesis. Covers both axes. Provides the inactive global-five upper toward both-marked opposite-axis-five singleton attainment; the saturated global-five bands and full selector remain open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_bound_le_global_threshold_of_global_axis_at_most_five_below_saturation (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (ha : 1 ≤ σ.a) (hu : 1 ≤ σ.u) (hak : σ.a ≤ σ.k) (huk : σ.u ≤ σ.k) (hsmall : σ.a ≤ 5 ∨ σ.u ≤ 5) (hbelow : σ.a+σ.u ≤ σ.k+3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ decomposableThreshold σ.a σ.u σ.k) ∧ σ.bound ≤ decomposableThreshold σ.a σ.u σ.k := by
  classical
  have hFour (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (ha : 1 ≤ σ.a) (hu : 1 ≤ σ.u)
  (hak : σ.a ≤ σ.k) (huk : σ.u ≤ σ.k)
  (hsmall : σ.a ≤ 4 ∨ σ.u ≤ 4) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ decomposableThreshold σ.a σ.u σ.k) ∧
  σ.bound ≤ decomposableThreshold σ.a σ.u σ.k := by
    classical
    have hSmallUpper (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (ha : 1 ≤ σ.a) (hu : 1 ≤ σ.u) (hak : σ.a ≤ σ.k) (huk : σ.u ≤ σ.k) (hsmall : σ.a ≤ 3 ∨ σ.u ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ decomposableThreshold σ.a σ.u σ.k) ∧ σ.bound ≤ decomposableThreshold σ.a σ.u σ.k := by
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
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    have hTriangle (ρ : Context)
        (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
        (s t : Side) (hne : s ≠ t)
        (hg : G ρ s ≤ 4) :
        ρ.bound ≤ (G ρ t).choose 2 := by
      let B := G ρ t
      let active := ρ.childPositions.toFinset.filter
        (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
      let I (p : ℕ) := Finset.Icc (ρ.leftExt t 0 p + 1) (B - 1 - ρ.rightExt t 0 p)
      let pairs := active.biUnion (fun p => ((I p).product (I p)).filter (fun z => z.1 ≤ z.2))
      let T := Finset.Icc 1 (B - 1)
      let triangle := (T.product T).filter (fun z => z.1 ≤ z.2)
      have hb := (ctx_small_global_axis_rank_pair_potential ρ hPos s t hne hg).2
      change ρ.bound ≤ pairs.card at hb
      have hInside (p : ℕ) : I p ⊆ T := by
        intro z hz
        have hh := Finset.mem_Icc.mp hz
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hSub : pairs ⊆ triangle := by
        intro z hz
        obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
        have hh := Finset.mem_filter.mp hz
        have hm := Finset.mem_product.mp hh.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨hInside p hm.1, hInside p hm.2⟩, hh.2⟩
      have hCardPairs (T : Finset ℕ) :
          ((T.product T).filter (fun z => z.1 ≤ z.2)).card = (T.card + 1).choose 2 := by
        rw [← Finset.card_sym2]
        apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
        · intro z hz
          exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
        · intro p hp q hq he
          have hpl := (Finset.mem_filter.mp hp).2
          have hql := (Finset.mem_filter.mp hq).2
          rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Prod.ext h1 h2
          · apply Prod.ext <;> omega
        · intro z hz
          induction z using Sym2.ind with
          | h a b =>
            obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
            by_cases hab : a ≤ b
            · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
            · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
                Sym2.eq_swap⟩
      have hTriangle : triangle.card = B.choose 2 := by
        change ((T.product T).filter (fun z => z.1 ≤ z.2)).card = B.choose 2
        rw [hCardPairs]
        by_cases hz : B = 0
        · norm_num [T, hz]
        · have hc : T.card + 1 = B := by
            simp only [T, Nat.card_Icc]
            omega
          rw [hc]
      exact hb.trans ((Finset.card_le_card hSub).trans_eq hTriangle)
    have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
        baseOf x y k = baseOf y x k := by
      have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
      have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
      apply Nat.le_antisymm
      · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
        simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
      · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
        simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    have hTopCup (K : ℕ) (hK : 4 ≤ K) :
        decomposableThreshold K 4 K = (K-2).choose 2+(K-1) := by
      rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have hw : decomposableBinomialWindow K 4 K = 1+(K-2)+(K-2).choose 2 := by
        norm_num [decomposableBinomialWindow,Finset.sum_Icc_succ_top]
      rw [hw]
      omega
    have hTopCap (K : ℕ) (hK : 4 ≤ K) :
        decomposableThreshold 4 K K = (K-2).choose 2+(K-1) := by
      have hs := hBaseSwap 3 (K-1) K (by omega) (by omega)
      unfold baseOf at hs
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)] at hs
      have he : K-1+1 = K := by omega
      simp only [he,show 3+1=4 by omega] at hs
      exact hs.symm.trans (hTopCup K hK)
    by_cases hthree : σ.a ≤ 3 ∨ σ.u ≤ 3
    · exact hSmallUpper σ hpositive ha hu hak huk hthree
    have ha4 : 4 ≤ σ.a := by omega
    have hu4 : 4 ≤ σ.u := by omega
    have hk4 : 4 ≤ σ.k := by omega
    have hFuel (fuel : ℕ) : boundFuel fuel σ ≤ σ.bound := by
      by_cases hf : σ.childPositions.length+1 ≤ fuel
      · exact (boundFuel_eq_bound σ hf).le
      · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
    have hBound : σ.bound ≤ decomposableThreshold σ.a σ.u σ.k := by
      rcases hsmall with hsmall | hsmall
      · have hae : σ.a=4 := by omega
        by_cases huBelow : σ.u ≤ σ.k-1
        · have ht : decomposableThreshold σ.a σ.u σ.k = σ.u.choose 2 := by
            rw [hae,decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
            have hr : 4+σ.u-4=σ.u := by omega
            simp only [hr,show 4-2=2 by omega]
          rw [ht]
          exact hTriangle σ hpositive Side.upper Side.lower (by decide)
            (by simpa [G,hae])
        · have hue : σ.u=σ.k := by omega
          have hb := (ctx_small_global_axis_saturated_triangle_bound σ hpositive
            Side.upper Side.lower (by decide) (by change σ.a ≤ 4; omega)
            (by change σ.u ≤ σ.k; exact huk) hk4).2.1
          rw [hae,hue,hTopCap σ.k hk4]
          exact hb
      · have hue : σ.u=4 := by omega
        by_cases haBelow : σ.a ≤ σ.k-1
        · have ht : decomposableThreshold σ.a σ.u σ.k = σ.a.choose 2 := by
            rw [hue,decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
            have hr : σ.a+4-4=σ.a := by omega
            rw [hr,Nat.choose_symm_of_eq_add (show σ.a=(σ.a-2)+2 by omega)]
          rw [ht]
          exact hTriangle σ hpositive Side.lower Side.upper (by decide)
            (by simpa [G,hue])
        · have hae : σ.a=σ.k := by omega
          have hb := (ctx_small_global_axis_saturated_triangle_bound σ hpositive
            Side.lower Side.upper (by decide) (by change σ.u ≤ 4; omega)
            (by change σ.a ≤ σ.k; exact hak) hk4).2.1
          rw [hae,hue,hTopCup σ.k hk4]
          exact hb
    exact ⟨fun fuel => (hFuel fuel).trans hBound,hBound⟩
  by_cases hfour : σ.a ≤ 4 ∨ σ.u ≤ 4
  · exact hFour σ hpositive ha hu hak huk hfour
  have ha5 : 5 ≤ σ.a := by omega
  have hu5 : 5 ≤ σ.u := by omega
  rcases hsmall with hsmall | hsmall
  · have hae : σ.a = 5 := by omega
    have hb := ctx_small_global_axis_rank_triple_potential σ hpositive
      Side.upper Side.lower (by decide) hsmall
    have ht :
        decomposableThreshold σ.a σ.u σ.k = (σ.u-1+2).choose 3 := by
      rw [hae,decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      simp only [show 5+σ.u-4 = σ.u-1+2 by omega,show 5-2 = 3 from rfl]
    rw [ht]
    exact ⟨fun fuel => (hb.1 fuel).trans hb.2.2.1,hb.2.1.trans hb.2.2.1⟩
  · have hue : σ.u = 5 := by omega
    have hb := ctx_small_global_axis_rank_triple_potential σ hpositive
      Side.lower Side.upper (by decide) hsmall
    have ht :
        decomposableThreshold σ.a σ.u σ.k = (σ.a-1+2).choose 3 := by
      rw [hue,decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      rw [show σ.a+5-4 = σ.a-1+2 by omega,
        Nat.choose_symm_of_eq_add (show σ.a-1+2 = (σ.a-2)+3 by omega)]
    rw [ht]
    exact ⟨fun fuel => (hb.1 fuel).trans hb.2.2.1,hb.2.1.trans hb.2.2.1⟩

end ErdosSzekeres
