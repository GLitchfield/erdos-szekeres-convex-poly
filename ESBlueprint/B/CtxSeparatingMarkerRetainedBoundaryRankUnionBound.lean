import ESBlueprint.B.CtxActiveBoundaryMarkerRankUnionBound
import ESBlueprint.B.CtxSeparatingMarkerEraseNormalize

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Linear opposite-rank union bound at global at most five when an indexed chosen marker separates all active source children and younger chosen positions from older chosen positions, and erasing it leaves a specified older boundary marker. All source children are active; arbitrary opposite history and maxima are retained. The separator normalization reduces the chosen global by one, exposes unchanged opposite traces and positive labels, and the existing active boundary rank theorem supplies the linear charge. Every fuel and the full bound are controlled. Provides exterior control for the proposed higher-capacity square estimate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_separating_marker_retained_boundary_rank_union_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j →
    ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x)
  (I y : ℕ) (hI : I ∈ σ.levels) (hNI : N < I)
  (hIs : σ.sideAt I = σ.sideAt N) (hy : y ∈ σ.extPositions I)
  (hretained : ∀ j ∈ σ.levelsOn (σ.sideAt N) I, j ≠ N →
    ∀ p ∈ σ.extPositions j, if rightward then p < y else y < p)
  (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion
    (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card) ∧ σ.bound ≤ ranks.card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ranks (ρ : Context) := (active ρ).biUnion
    (fun p => Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ t - 1 - ρ.rightExt t 0 p))
  let ρ : Context := { σ with
    word := σ.word.map (fun z => match z with
      | Letter.child => Letter.child
      | Letter.ext j v => Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v)
    maxima := σ.maxima.eraseIdx (N - 1) }
  let τ : Context := match σ.sideAt N with
    | Side.lower => { ρ with u := σ.u - 1 }
    | Side.upper => { ρ with a := σ.a - 1 }
  let up (j : ℕ) := if j < N then j else j + 1
  let J := I - 1
  change (∀ fuel, boundFuel fuel σ ≤ (ranks σ).card) ∧ σ.bound ≤ (ranks σ).card
  have hh := ctx_separating_marker_erase_normalize σ hpositive N x hN hx rightward
    hchildren hyounger holder
  have hChild : τ.childPositions = σ.childPositions := hh.1
  have hDepth : τ.maxima.length = σ.maxima.length - 1 := hh.2.1
  have hTransport : ∀ j ∈ τ.levels,
      up j ∈ σ.levels ∧ up j ≠ N ∧ τ.extPositions j = σ.extPositions (up j) ∧
        τ.sideAt j = σ.sideAt (up j) ∧ τ.maximumAt j = σ.maximumAt (up j) := hh.2.2.1
  have hOpp : ∀ p, τ.leftExt t 0 p = σ.leftExt t 0 p ∧
      τ.rightExt t 0 p = σ.rightExt t 0 p := hh.2.2.2.1 t hne
  have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hh.2.2.2.2.1
  have hLimits : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q := hh.2.2.2.2.2.1
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hh.2.2.2.2.2.2.1
  have hBound : σ.bound ≤ τ.bound := hh.2.2.2.2.2.2.2
  have hLevelMem (υ : Context) (j : ℕ) : j ∈ υ.levels ↔ 1 ≤ j ∧ j ≤ υ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hN1 := one_le_of_mem_levels hN
  have hILimit := (hLevelMem σ I).mp hI
  have hJ1 : 1 ≤ J := by dsimp [J]; omega
  have hJ : J ∈ τ.levels := by
    apply (hLevelMem τ J).mpr
    rw [hDepth]
    dsimp [J]
    omega
  have hUpJ : up J = I := by
    have hJN : ¬J < N := by dsimp [J]; omega
    simp only [up, if_neg hJN]
    dsimp [J]
    omega
  have hSide : τ.sideAt J = σ.sideAt N := by
    rw [(hTransport J hJ).2.2.2.1, hUpJ, hIs]
  have hY : y ∈ τ.extPositions J := by
    rw [(hTransport J hJ).2.2.1, hUpJ]
    exact hy
  have hIOn : I ∈ σ.levelsOn (σ.sideAt N) 0 :=
    List.mem_filter.mpr ⟨hI, by simp [hIs]⟩
  have hXY := holder I hIOn hNI y hy
  have hNear : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p →
      if rightward then p < y else y < p := by
    intro p hp _
    rw [hChild] at hp
    have hc := hchildren p hp
    cases rightward <;> simp only [Bool.false_eq_true, if_false, if_true] at hc hXY ⊢ <;> omega
  have hYoung : ∀ j ∈ τ.levelsOn (τ.sideAt J) J, ∀ p ∈ τ.extPositions j,
      if rightward then p < y else y < p := by
    intro j hj p hp
    have hjl := (List.mem_filter.mp hj).1
    have hjc : τ.sideAt j = τ.sideAt J ∧ (J = 0 ∨ j < J) :=
      of_decide_eq_true (List.mem_filter.mp hj).2
    have hjJ : j < J := by omega
    have hT := hTransport j hjl
    have hUpI : up j < I := by
      have hjJ' : j < I - 1 := hjJ
      dsimp only [up]
      split_ifs <;> omega
    have hSourceOn : up j ∈ σ.levelsOn (σ.sideAt N) I := by
      apply List.mem_filter.mpr
      refine ⟨hT.1, ?_⟩
      apply decide_eq_true
      refine ⟨?_, Or.inr hUpI⟩
      rw [← hT.2.2.2.1, hjc.1, hSide]
    rw [hT.2.2.1] at hp
    exact hretained (up j) hSourceOn hT.2.1 p hp
  have hChosenG : G τ (σ.sideAt N) = G σ (σ.sideAt N) - 1 := by
    cases hs : σ.sideAt N <;> simp only [τ, ρ, G, hs]
  have hOppG : G τ t = G σ t := by
    cases hs : σ.sideAt N
    · have ht : t = Side.upper := by
        cases t with
        | lower => exact False.elim (hne hs)
        | upper => rfl
      subst t
      simp only [τ, ρ, G, hs]
    · have ht : t = Side.lower := by
        cases t with
        | lower => rfl
        | upper => exact False.elim (hne hs)
      subst t
      simp only [τ, ρ, G, hs]
  have hSmall : min (G τ (τ.sideAt J) - 1) (τ.k - τ.maximumAt J) ≤ 3 := by
    have hg : G σ (σ.sideAt N) ≤ 5 := hglobal
    rw [hSide, hChosenG]
    omega
  have hActive : active τ = active σ := by
    ext p
    simp only [active, Finset.mem_filter, List.mem_toFinset, hChild]
    constructor
    · intro hp
      exact ⟨hp.1, hactive p hp.1⟩
    · intro hp
      have hL := hLimits p hp.1 p hp.1
      exact ⟨hp.1, lt_of_lt_of_le hp.2.1 hL.1, lt_of_lt_of_le hp.2.2 hL.2⟩
  have hInterval (p : ℕ) :
      Finset.Icc (τ.leftExt t 0 p + 1) (G τ t - 1 - τ.rightExt t 0 p) =
        Finset.Icc (σ.leftExt t 0 p + 1) (G σ t - 1 - σ.rightExt t 0 p) := by
    rw [(hOpp p).1, (hOpp p).2, hOppG]
  have hRanks : ranks τ = ranks σ := by
    simp only [ranks, hActive, hInterval]
  have hNe : τ.sideAt J ≠ t := by rw [hSide]; exact hne
  have hLinear := ctx_active_boundary_marker_rank_union_bound τ hPos J y hJ hY rightward
    hNear hYoung t hNe hSmall
  change (∀ fuel, boundFuel fuel τ ≤ (ranks τ).card) ∧ τ.bound ≤ (ranks τ).card at hLinear
  rw [hRanks] at hLinear
  exact ⟨fun fuel => (hFuel fuel).trans (hLinear.1 fuel), hBound.trans hLinear.2⟩

end ErdosSzekeres
