import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinFourRankTopBandPotential
import ESBlueprint.B.CtxThinFourRankNextBandPotential
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Turn the top and next four-rank saturation bounds into the actual-marker geometry needed by exterior cut arguments. The nonmonotone triple forces two chosen chain losses everywhere, placing active intervals in a thin four-rank window; a large chosen maximum then yields 3k-8, or 3k-9 in the next opposite band.
Positive labels, distinct axes, three actual chosen levels in a nonmonotone age/spatial order, chosen global at most five, opposite global at most k, and k at least five.
Empty indexed opposite history and some indexed chosen maximum at least k-4. The selected large level need not be one of the three actual levels and need not have an actual occurrence.
The sharper second conclusion requires opposite global at most k-1. No exact-depth, child pattern or recursive potential premise. The large-maximum and empty-history restrictions remain.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_triple_saturated_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (J N M z x y : ℕ)
  (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
  (hJN : J < N) (hNM : N < M)
  (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hz : z ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 5 ≤ σ.k) (R : ℕ) (hR : R ∈ σ.levels) (hRs : σ.sideAt R = s)
  (hmaximum : σ.k-4 ≤ σ.maximumAt R) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3*σ.k-8) ∧ σ.bound ≤ 3*σ.k-8 ∧
    ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k-1 →
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3*σ.k-9) ∧ σ.bound ≤ 3*σ.k-9) := by
  classical
  have ctx_nonmonotone_triple_chosen_chain_loss (σ : Ctx.Context) (s : Ctx.Side) (J N M z x y : ℕ)
    (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
    (hJN : J < N) (hNM : N < M)
    (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (hz : z ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y)) :
    ∀ p ∈ σ.childPositions, 2 ≤ σ.chainExt s p p := by
    classical
    have hJOn : J ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hJ, by simp [hJs]⟩
    have hFirst := ctx_chain_one_children_exterior_of_two_levels σ s J N z x
      hJ hN hJN hJs hNs hz hx
    have hSecond := ctx_chain_one_children_exterior_of_two_levels σ s N M x y
      hN hM hNM hNs hMs hx hy
    intro p hp
    by_contra h
    have hc : σ.chainExt s p p ≤ 1 := by omega
    rcases hgeometry with hgeometry | hgeometry
    · rcases hFirst with hFirst | hFirst
      · rcases hSecond with hSecond | hSecond
        · omega
        · have hzp := hFirst.2 p hp hc J hJOn z hz
          have hpz := hSecond.2 p hp hc J hJOn z hz
          omega
      · omega
    · rcases hFirst with hFirst | hFirst
      · omega
      · rcases hSecond with hSecond | hSecond
        · have hpz := hFirst.2 p hp hc J hJOn z hz
          have hzp := hSecond.2 p hp hc J hJOn z hz
          omega
        · omega

  let G (v : Side) := match v with | Side.lower => σ.u | Side.upper => σ.a
  have hg : G s ≤ 5 := by cases s <;> exact hglobal
  have hLoss := ctx_nonmonotone_triple_chosen_chain_loss σ s J N M z x y
    hJ hN hM hJN hNM hJs hNs hMs hz hx hy hgeometry
  have hThin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      G s-1-σ.rightExt s 0 p ≤ σ.leftExt s 0 p+2 := by
    intro p hp _ _
    have hh := hLoss p hp
    dsimp only [chainExt] at hh
    omega
  have hWindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      1 ≤ σ.leftExt s 0 p+1 ∧ G s-1-σ.rightExt s 0 p ≤ 1+3 := by
    intro p hp _ _
    constructor <;> omega
  have htop := ctx_thin_four_rank_top_band_potential σ hpositive s t hne hclear
    (by cases t <;> exact hopposite) hk R hR hRs hmaximum 1 (by cases s <;> exact hThin)
    (by cases s <;> exact hWindow)
  refine ⟨htop.1,htop.2,?_⟩
  intro hnext
  exact ctx_thin_four_rank_next_band_potential σ hpositive s t hne hclear
    (by cases t <;> exact hnext) hk R hR hRs hmaximum 1 (by cases s <;> exact hThin)
    (by cases s <;> exact hWindow)


end ErdosSzekeres
