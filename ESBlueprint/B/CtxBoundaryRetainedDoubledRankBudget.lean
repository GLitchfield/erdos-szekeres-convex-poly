import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Normalize at a retained outer boundary marker, discard all newer history, and bound the remaining one-level context by twice the residual opposite-rank width minus one. Uniform left and right reservations below the outer marker are retained. Positive labels, arbitrary older history, both axes and directions, inactive children, and zero residual width remain explicit. This standalone theorem replaces a repeated local argument in surrounding-marker cut proofs; exact search found no registered equivalent.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_boundary_marker_upper_normalize, ErdosSzekeres.ctx_one_level_refined_potential_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_boundary_retained_doubled_rank_budget (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (N J x y : ℕ) (hN : N ∈ σ.levels) (hJ : J ∈ σ.levels) (hJN : J < N) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions J) (hside : σ.sideAt J = σ.sideAt N) (outer : Bool) (hOuter : ∀ p ∈ σ.childPositions, if outer then p < x else x < p) (hOuterYoung : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, if outer then p < x else x < p) (t : Ctx.Side) (hne : σ.sideAt N ≠ t) (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (A B : ℕ) (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t N p) (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t N p) : let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * budget - 1) ∧ σ.bound ≤ 2 * budget - 1 := by
  classical
  let τ : Context := match (generalizing := false) σ.sideAt N with
    | Side.lower =>
        { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    | Side.upper =>
        { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
  let w := (match (generalizing := false) t with
    | Side.lower => σ.u
    | Side.upper => σ.a) - 1
  change (∀ fuel, boundFuel fuel σ ≤ 2 * (w - A - B) - 1) ∧
    σ.bound ≤ 2 * (w - A - B) - 1
  have hNorm := ctx_boundary_marker_upper_normalize σ hpositive N x hN hx outer hOuter hOuterYoung
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1
  have hFull : σ.bound ≤ τ.bound := hNorm.2.2
  have hWord : τ.word = σ.word := by cases hs : σ.sideAt N <;> simp only [τ, hs]
  have hMaxima : τ.maxima = σ.maxima.take (N - 1) := by
    cases hs : σ.sideAt N <;> simp only [τ, hs]
  have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by simp only [letterAt, hWord]
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
  have hLevelMem (ρ : Context) (j : ℕ) :
      j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hj
      exact ⟨j - 1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x + 1)
      (fun a b hab => Nat.add_lt_add_right hab 1)
  have hLevels : τ.levels = σ.levels.filter (· < N) := by
    apply (hSorted τ).eq_of_mem_iff ((hSorted σ).filter _)
    intro j
    simp only [List.mem_filter, hLevelMem, hMaxima, List.length_take,
      decide_eq_true_eq]
    omega
  have hLevelsOn (v : Side) (top : ℕ) :
      τ.levelsOn v top = (σ.levelsOn v top).filter (· < N) := by
    simp only [levelsOn, hLevels, hSide, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp only [Bool.and_comm]
  have hNpos := one_le_of_mem_levels hN
  have hJτ : J ∈ τ.levels := by
    rw [hLevels]
    exact List.mem_filter.mpr ⟨hJ, by simp [hJN]⟩
  have hBelow (v : Side) : τ.levelsOn v 0 = σ.levelsOn v N := by
    rw [hLevelsOn]
    simp only [levelsOn, List.filter_filter]
    apply List.filter_congr
    intro j hj
    by_cases hv : σ.sideAt j = v <;> by_cases hjN : j < N <;>
      simp [hv, hjN, show N ≠ 0 by omega]
  have hLeftStep : leftStep τ = leftStep σ := by
    funext z j
    simp only [leftStep, hExt]
  have hRightStep : rightStep τ = rightStep σ := by
    funext z j
    simp only [rightStep, hExt]
  have hLeftEq (p : ℕ) : τ.leftExt t 0 p = σ.leftExt t N p := by
    simp only [leftExt_eq, hLeftStep, hBelow]
  have hRightEq (p : ℕ) : τ.rightExt t 0 p = σ.rightExt t N p := by
    simp only [rightExt_eq, hRightStep, hBelow]
  have hChosen : (match (generalizing := false) τ.sideAt J with
      | Side.lower => τ.u
      | Side.upper => τ.a) ≤ 4 := by
    rw [hSide, hside]
    cases hs : σ.sideAt N
    · simp only [τ, hs] at hglobal ⊢
      exact (Nat.min_le_left (σ.u - 1) (σ.k - σ.maximumAt N)).trans (by omega)
    · simp only [τ, hs] at hglobal ⊢
      exact (Nat.min_le_left (σ.a - 1) (σ.k - σ.maximumAt N)).trans (by omega)
  let budget := (match (generalizing := false) t with
    | Side.lower => τ.u
    | Side.upper => τ.a) - 1
  have hBudget : budget = w := by
    dsimp only [budget, τ, w]
    cases hs : σ.sideAt N <;> cases ht : t <;>
      simp_all only [ne_eq, not_true_eq_false]
  let active := τ.childPositions.toFinset.filter
    (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
  let I (p : ℕ) := Finset.Icc (τ.leftExt t 0 p + 1) (budget - τ.rightExt t 0 p)
  let ranks := active.biUnion I
  have hh := ctx_one_level_refined_potential_bound τ hPositive (τ.sideAt J) t
    (by rw [hSide, hside]; exact hne) J y hJτ rfl (by rw [hExt]; exact hy) hChosen
  have hRf : ∀ fuel, boundFuel fuel τ ≤ 2 * ranks.card - 1 := by
    intro fuel
    exact (hh.1 fuel).trans (Nat.min_le_right _ _)
  have hRb : τ.bound ≤ 2 * ranks.card - 1 :=
    hh.2.1.trans (Nat.min_le_right _ _)
  have hsub : ranks ⊆ Finset.Icc (A + 1) (w - B) := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hc : p ∈ σ.childPositions := by
      rw [← hChild]
      exact List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hL : A ≤ τ.leftExt t 0 p := by rw [hLeftEq]; exact hLeft p hc
    have hR : B ≤ τ.rightExt t 0 p := by rw [hRightEq]; exact hRight p hc
    have hz' : τ.leftExt t 0 p + 1 ≤ z ∧ z ≤ budget - τ.rightExt t 0 p :=
      Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hc : ranks.card ≤ w - A - B := by
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    omega
  have hFinal : 2 * ranks.card - 1 ≤ 2 * (w - A - B) - 1 := by omega
  exact ⟨fun fuel => (hFuel fuel).trans ((hRf fuel).trans hFinal),
    hFull.trans (hRb.trans hFinal)⟩

end ErdosSzekeres
