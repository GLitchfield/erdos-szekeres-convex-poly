import ESBlueprint.B.CtxBoundaryMarkerRankBudget

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Normalize at an outer boundary marker, retain an inner same-side boundary marker, and charge uniform left and right opposite-axis rank reservations below the inner level. This standalone form replaces a repeatedly duplicated local argument in two-marker endpoint and internal-cut bounds. Positive labels, arbitrary histories, both directions and axes, inactive children, and zero residual budget remain explicit. Exact searches found no registered equivalent.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_boundary_marker_upper_normalize, ErdosSzekeres.ctx_boundary_marker_rank_budget
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nested_boundary_markers_rank_budget (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (N J x y : ℕ) (hN : N ∈ σ.levels) (hJ : J ∈ σ.levels) (hJN : J < N) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions J) (hside : σ.sideAt J = σ.sideAt N) (outer inner : Bool) (hOuter : ∀ p ∈ σ.childPositions, if outer then p < x else x < p) (hOuterYoung : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, if outer then p < x else x < p) (hInner : ∀ p ∈ σ.childPositions, if inner then p < y else y < p) (hInnerYoung : ∀ j ∈ σ.levelsOn (σ.sideAt J) J, ∀ p ∈ σ.extPositions j, if inner then p < y else y < p) (t : Ctx.Side) (hne : σ.sideAt N ≠ t) (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (A B : ℕ) (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t J p) (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t J p) : let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
  classical
  let τ : Context := match (generalizing := false) σ.sideAt N with
    | Side.lower =>
        { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    | Side.upper =>
        { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
  let w := (match (generalizing := false) t with
    | Side.lower => σ.u
    | Side.upper => σ.a) - 1
  change (∀ fuel, boundFuel fuel σ ≤ w - A - B) ∧ σ.bound ≤ w - A - B
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
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
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
  have hJpos := one_le_of_mem_levels hJ
  have hJτ : J ∈ τ.levels := by
    rw [hLevels]
    exact List.mem_filter.mpr ⟨hJ, by simp [hJN]⟩
  have hBelow (v : Side) : τ.levelsOn v J = σ.levelsOn v J := by
    rw [hLevelsOn]
    apply List.filter_eq_self.mpr
    intro j hj
    have hh := of_decide_eq_true (List.mem_filter.mp hj).2
    simp only [decide_eq_true_eq]
    omega
  have hLeftStep : leftStep τ = leftStep σ := by
    funext z j
    simp only [leftStep, hExt]
  have hRightStep : rightStep τ = rightStep σ := by
    funext z j
    simp only [rightStep, hExt]
  have hLeftEq (p : ℕ) : τ.leftExt t J p = σ.leftExt t J p := by
    simp only [leftExt_eq, hLeftStep, hBelow]
  have hRightEq (p : ℕ) : τ.rightExt t J p = σ.rightExt t J p := by
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
  have hSmall : min ((match (generalizing := false) τ.sideAt J with
      | Side.lower => τ.u
      | Side.upper => τ.a) - 1) (τ.k - τ.maximumAt J) ≤ 3 := by
    apply (Nat.min_le_left _ _).trans
    omega
  have hBudget : (match (generalizing := false) t with
      | Side.lower => τ.u
      | Side.upper => τ.a) - 1 = w := by
    dsimp only [τ, w]
    cases hs : σ.sideAt N <;> cases ht : t <;>
      simp_all only [ne_eq, not_true_eq_false]
  have hBound := ctx_boundary_marker_rank_budget τ hPositive J y hJτ
    (by rw [hExt]; exact hy) inner
    (by intro p hp; rw [hChild] at hp; exact hInner p hp)
    (by
      intro j hj p hp
      rw [hSide, hBelow] at hj
      rw [hExt] at hp
      exact hInnerYoung j hj p hp)
    t (by rw [hSide, hside]; exact hne) hSmall A B
    (by intro p hp; rw [hChild] at hp; rw [hLeftEq]; exact hLeft p hp)
    (by intro p hp; rw [hChild] at hp; rw [hRightEq]; exact hRight p hp)
  change (∀ fuel, boundFuel fuel τ ≤
      ((match (generalizing := false) t with
        | Side.lower => τ.u
        | Side.upper => τ.a) - 1) - A - B) ∧
    τ.bound ≤ ((match (generalizing := false) t with
      | Side.lower => τ.u
      | Side.upper => τ.a) - 1) - A - B at hBound
  rw [hBudget] at hBound
  exact ⟨fun fuel => (hFuel fuel).trans (hBound.1 fuel), hFull.trans hBound.2⟩

end ErdosSzekeres
