import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A quantitative opposite-rank budget after boundary-marker normalization. If the normalized parameter on the marker side is at most three, subtract uniform left and right opposite-axis extension bounds below the marker level from the opposite global budget. Bounds every fuel approximation and the full recursive bound, in either direction and axis, including zero capacities and empty children. Combines boundary normalization with the small-axis rank-region potential, retaining the loss from one or two removed boundaries in one-sided uniform-gap parts.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_boundary_marker_rank_budget (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (σ.k - σ.maximumAt N) ≤ 3)
  (A B : ℕ)
  (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t N p)
  (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t N p) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
  classical
  let τ : Context := match σ.sideAt N with
    | Side.lower => { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    | Side.upper => { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
  let P := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let active : Finset ℕ := τ.childPositions.toFinset.filter
    (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
  let ranks := active.biUnion (fun p => Finset.Icc (τ.leftExt t 0 p + 1) (P - τ.rightExt t 0 p))
  change (∀ fuel, boundFuel fuel σ ≤ P - A - B) ∧ σ.bound ≤ P - A - B
  have hNorm := ctx_boundary_marker_upper_normalize σ hpositive N x hN hx rightward hchildren hyounger
  have hNormFuel (fuel : ℕ) : boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1 fuel
  have hN1 : 1 ≤ N := one_le_of_mem_levels hN
  have hWord : τ.word = σ.word := by
    cases hs : σ.sideAt N <;> simp only [τ, hs]
  have hMaxima : τ.maxima = σ.maxima.take (N - 1) := by
    cases hs : σ.sideAt N <;> simp only [τ, hs]
  have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
    simp only [letterAt, hWord]
  have hChild : τ.childPositions = σ.childPositions := by
    simp only [childPositions, hWord, hLetter]
  have hExt (j : ℕ) : τ.extPositions j = σ.extPositions j := by
    simp only [extPositions, hWord, hLetter]
  have hSide (j : ℕ) : τ.sideAt j = σ.sideAt j := by
    simp only [sideAt, hExt, hLetter]
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hLetter] at hp
    exact hpositive p j v hp
  have hSmall : (match σ.sideAt N with | Side.lower => τ.u | Side.upper => τ.a) ≤ 3 := by
    cases hs : σ.sideAt N <;> simpa only [τ, hs] using hsmall
  have hBudget : (fun v : Side => match v with | Side.lower => τ.u - 1 | Side.upper => τ.a - 1) t = P := by
    dsimp only [τ, P]
    cases hs : σ.sideAt N <;> cases ht : t <;> simp_all only [ne_eq, not_true_eq_false]
  have hLeftStep : leftStep τ = leftStep σ := by
    funext z j
    simp only [leftStep, hExt]
  have hRightStep : rightStep τ = rightStep σ := by
    funext z j
    simp only [rightStep, hExt]
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hj
      exact ⟨j - 1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b hab => Nat.add_lt_add_right hab 1)
  have hLevels : τ.levels = σ.levels.filter (· < N) := by
    apply (hSorted τ).eq_of_mem_iff ((hSorted σ).filter _)
    intro j
    simp only [List.mem_filter, hLevelMem, hMaxima, List.length_take, decide_eq_true_eq]
    omega
  have hPureLevels (v : Side) : τ.levelsOn v 0 = σ.levelsOn v N := by
    simp only [levelsOn, hLevels, hSide, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp [show N ≠ 0 by omega, Bool.and_comm]
  have hPureLeft (v : Side) (p : ℕ) : τ.leftExt v 0 p = σ.leftExt v N p := by
    simp only [leftExt_eq, hPureLevels, hLeftStep]
  have hPureRight (v : Side) (p : ℕ) : τ.rightExt v 0 p = σ.rightExt v N p := by
    simp only [rightExt_eq, hPureLevels, hRightStep]
  have hPotential := ctx_small_global_axis_rank_region_potential τ hPositive (σ.sideAt N) t hne hSmall
  have hTauFuel (fuel : ℕ) : boundFuel fuel τ ≤ ranks.card := by
    have h := hPotential.1 fuel
    dsimp only at h hBudget
    split_ifs at h
    · cases ht : t <;> simp only [ht] at h hBudget <;>
        simpa only [ranks, active, ht, hBudget] using h
    · have h' := h.trans (Nat.min_le_right _ _)
      cases ht : t <;> simp only [ht] at h' hBudget <;>
        simpa only [ranks, active, ht, hBudget] using h'
  have hSubset : ranks ⊆ Finset.Icc (A + 1) (P - B) := by
    intro r hr
    obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
    have hpChild : p ∈ τ.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    rw [hChild] at hpChild
    have hl := hLeft p hpChild
    have hr' := hRight p hpChild
    rw [← hPureLeft t p] at hl
    rw [← hPureRight t p] at hr'
    have hI := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hCard : ranks.card ≤ P - A - B := by
    calc
      ranks.card ≤ (Finset.Icc (A + 1) (P - B)).card := Finset.card_le_card hSubset
      _ = P - A - B := by rw [Nat.card_Icc]; omega
  have hAll (fuel : ℕ) : boundFuel fuel σ ≤ P - A - B :=
    (hNormFuel fuel).trans ((hTauFuel fuel).trans hCard)
  exact ⟨hAll, by simpa only [bound] using hAll (σ.childPositions.length + 1)⟩

end ErdosSzekeres
