import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.CtxSeparatingMarkerEraseNormalize

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A doubled opposite-rank-union bound for a context with a separating marker at chosen global at most five and any distinct surviving actual marker on the same axis. Every source child is active; the retained marker can be younger or older and need not itself be a boundary. Erase the separator with a one-unit chosen-global reduction, transport the entire opposite history, and apply the checked global-four actual-marker potential. Bounds every recursive fuel and the full value by twice the exact source rank-union cardinality minus one. This is a reusable adjacent-zone charge after suitable occurrence pruning; no general global-five square bound is asserted.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_separating_marker_retained_level_doubled_rank_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j →
    ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x)
  (I y : ℕ) (hI : I ∈ σ.levels) (hNI : I ≠ N)
  (hIs : σ.sideAt I = σ.sideAt N) (hy : y ∈ σ.extPositions I)
  (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion
    (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * ranks.card - 1) ∧ σ.bound ≤ 2 * ranks.card - 1 := by
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
  let J := if I < N then I else I - 1
  change (∀ fuel, boundFuel fuel σ ≤ 2 * (ranks σ).card - 1) ∧ σ.bound ≤ 2 * (ranks σ).card - 1
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
  have hJ1 : 1 ≤ J := by
    dsimp only [J]
    split_ifs <;> omega
  have hJ : J ∈ τ.levels := by
    apply (hLevelMem τ J).mpr
    rw [hDepth]
    have hNLimit := (hLevelMem σ N).mp hN
    dsimp only [J]
    split_ifs <;> omega
  have hUpJ : up J = I := by
    dsimp only [up, J]
    split_ifs <;> omega
  have hSide : τ.sideAt J = σ.sideAt N := by
    rw [(hTransport J hJ).2.2.2.1, hUpJ, hIs]
  have hY : y ∈ τ.extPositions J := by
    rw [(hTransport J hJ).2.2.1, hUpJ]
    exact hy
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
  have hSmall : G τ (σ.sideAt N) ≤ 4 := by
    have hg : G σ (σ.sideAt N) ≤ 5 := hglobal
    rw [hChosenG]
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
  have hDoubled := ctx_one_level_refined_potential_bound τ hPos (σ.sideAt N) t hne
    J y hJ hSide hY hSmall
  have hFuelDoubled (fuel : ℕ) : boundFuel fuel τ ≤ 2 * (ranks τ).card - 1 :=
    (hDoubled.1 fuel).trans (Nat.min_le_right _ _)
  have hBoundDoubled : τ.bound ≤ 2 * (ranks τ).card - 1 :=
    hDoubled.2.1.trans (Nat.min_le_right _ _)
  rw [hRanks] at hFuelDoubled hBoundDoubled
  exact ⟨fun fuel => (hFuel fuel).trans (hFuelDoubled fuel), hBound.trans hBoundDoubled⟩

end ErdosSzekeres
