import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Bound a context containing a nonmonotone actual chosen triple by three times the opposite width minus two. The actual triple forces two pure chosen chain losses everywhere; at chosen global at most five all active chosen intervals have width at most two, and the one-cluster rank-rectangle cover pays the recurrence. Positive physical labels, distinct axes, chosen global at most five and opposite width at least one. Three actual indexed chosen levels J<N<M have positions z,x,y with x strictly to the same side of both z and y; this covers all four nonmonotone age/spatial orders. Arbitrary additional chosen and opposite history, maxima, inactive children and physical external barriers are allowed. No recursive bound or bare-history premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_triple_linear_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (J N M z x y : ℕ)
  (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
  (hJN : J < N) (hNM : N < M)
  (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hz : z ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hwidth : 1 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3 * w - 2) ∧ σ.bound ≤ 3 * w - 2 := by
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

  classical
  let G (v : Side) := match v with | Side.lower => σ.u | Side.upper => σ.a
  let w := G t - 1
  let active := σ.childPositions.toFinset.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks (v : Side) (p : ℕ) := Finset.Icc (σ.leftExt v 0 p + 1) (G v - 1 - σ.rightExt v 0 p)
  let cost (I : Finset ℕ) := if I = ∅ then 0 else
    ((I.biUnion (ranks s)).card - 1) * ((I.biUnion (ranks t)).card - 1) + 1
  change (∀ fuel, boundFuel fuel σ ≤ 3 * w - 2) ∧ σ.bound ≤ 3 * w - 2
  have hw : 1 ≤ w := hwidth
  have hg : G s ≤ 5 := hglobal
  have hLoss := ctx_nonmonotone_triple_chosen_chain_loss σ s J N M z x y
    hJ hN hM hJN hNM hJs hNs hMs hz hx hy hgeometry
  have hThin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      G s - 1 - σ.rightExt s 0 p ≤ σ.leftExt s 0 p + 2 := by
    intro p hp _ _
    have hl := hLoss p hp
    dsimp only [chainExt] at hl
    omega
  have hCover := ctx_thin_rank_rectangle_context_cover_potential σ hpositive s t hne
    (by cases s <;> exact hThin)
    [active] (fun p hp => ⟨active, by simp, hp⟩)
    (by intro I hI; have he := List.mem_singleton.mp hI; subst I; exact Finset.Subset.refl _)
  change (∀ fuel, boundFuel fuel σ ≤ ([active].map cost).sum) ∧
    σ.bound ≤ ([active].map cost).sum at hCover
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hCover
  have hBudget : cost active ≤ 3 * w - 2 := by
    by_cases hEmpty : active = ∅
    · simp only [cost, if_pos hEmpty]
      exact Nat.zero_le _
    have hRankSub (v : Side) : active.biUnion (ranks v) ⊆ Finset.Icc 1 (G v - 1) := by
      intro z hz
      obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hRankCard (v : Side) : (active.biUnion (ranks v)).card ≤ G v - 1 := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card (hRankSub v)
    have hxCard : (active.biUnion (ranks s)).card - 1 ≤ 3 := by
      have hh := hRankCard s
      omega
    have hyCard : (active.biUnion (ranks t)).card - 1 ≤ w - 1 := by
      have hh := hRankCard t
      dsimp only [w]
      omega
    have hh := Nat.mul_le_mul hxCard hyCard
    have he : 3 * (w - 1) + 1 = 3 * w - 2 := by omega
    simp only [cost, if_neg hEmpty]
    omega
  exact ⟨fun fuel => (hCover.1 fuel).trans hBudget, hCover.2.trans hBudget⟩

end ErdosSzekeres
