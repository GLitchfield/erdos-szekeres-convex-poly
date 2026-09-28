import ESBlueprint.B.CtxTwoMarkerOlderExteriorEndpointCutPotentialBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- When the retained endpoint lies strictly between two actual chosen markers, the chosen complement has nested boundary budget w, and the opposite companion has nested budget w-1 using the new exterior opposite marker. Prove the full and arbitrary independent fuel cut sum is at most 2w-1, allowing arbitrary positive histories, old maxima, inactive children, physical barriers, and independent new maxima.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_between_endpoint_cut_doubled_rank_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 1 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ l m n : ℕ)
  (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep)
  (hbetween : (∀ p ∈ keep, x < p ∧ p < y) ∨ (∀ p ∈ keep, y < p ∧ p < x))
  (hendpoint :
    (∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p) ∨
    (∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q)) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
    Ctx.Context.boundFuel g (σ.part keep t n) ≤ 2 * w - 1) ∧
    (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 2 * w - 1 := by
  classical
  have ctx_nested_boundary_markers_rank_budget (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N J x y : ℕ) (hN : N ∈ σ.levels) (hJ : J ∈ σ.levels) (hJN : J < N)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions J)
    (hside : σ.sideAt J = σ.sideAt N)
    (outer inner : Bool)
    (hOuter : ∀ p ∈ σ.childPositions, if outer then p < x else x < p)
    (hOuterYoung : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if outer then p < x else x < p)
    (hInner : ∀ p ∈ σ.childPositions, if inner then p < y else y < p)
    (hInnerYoung : ∀ j ∈ σ.levelsOn (σ.sideAt J) J, ∀ p ∈ σ.extPositions j,
      if inner then p < y else y < p)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (A B : ℕ)
    (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t J p)
    (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t J p) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
    classical
    let τ : Context := match (generalizing := false) σ.sideAt N with
      | Side.lower => { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
      | Side.upper => { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    change (∀ fuel, boundFuel fuel σ ≤ w - A - B) ∧ σ.bound ≤ w - A - B
    have hNorm := ctx_boundary_marker_upper_normalize σ hpositive N x hN hx outer hOuter hOuterYoung
    have hFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1
    have hFull : σ.bound ≤ τ.bound := hNorm.2.2
    have hWord : τ.word = σ.word := by cases hs : σ.sideAt N <;> simp only [τ, hs]
    have hMaxima : τ.maxima = σ.maxima.take (N - 1) := by cases hs : σ.sideAt N <;> simp only [τ, hs]
    have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by simp only [letterAt, hWord]
    have hChild : τ.childPositions = σ.childPositions := by simp only [childPositions, hWord, hLetter]
    have hExt (j : ℕ) : τ.extPositions j = σ.extPositions j := by simp only [extPositions, hWord, hLetter]
    have hSide (j : ℕ) : τ.sideAt j = σ.sideAt j := by simp only [sideAt, hExt, hLetter]
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
      exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b hab => Nat.add_lt_add_right hab 1)
    have hLevels : τ.levels = σ.levels.filter (· < N) := by
      apply (hSorted τ).eq_of_mem_iff ((hSorted σ).filter _)
      intro j
      simp only [List.mem_filter, hLevelMem, hMaxima, List.length_take, decide_eq_true_eq]
      omega
    have hLevelsOn (v : Side) (top : ℕ) : τ.levelsOn v top = (σ.levelsOn v top).filter (· < N) := by
      simp only [levelsOn, hLevels, hSide, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp only [Bool.and_comm]
    have hJpos := one_le_of_mem_levels hJ
    have hJτ : J ∈ τ.levels := by rw [hLevels]; exact List.mem_filter.mpr ⟨hJ, by simp [hJN]⟩
    have hBelow (v : Side) : τ.levelsOn v J = σ.levelsOn v J := by
      rw [hLevelsOn]
      apply List.filter_eq_self.mpr
      intro j hj
      have hh := of_decide_eq_true (List.mem_filter.mp hj).2
      simp only [decide_eq_true_eq]
      omega
    have hLeftStep : leftStep τ = leftStep σ := by funext z j; simp only [leftStep, hExt]
    have hRightStep : rightStep τ = rightStep σ := by funext z j; simp only [rightStep, hExt]
    have hLeftEq (p : ℕ) : τ.leftExt t J p = σ.leftExt t J p := by
      simp only [leftExt_eq, hLeftStep, hBelow]
    have hRightEq (p : ℕ) : τ.rightExt t J p = σ.rightExt t J p := by
      simp only [rightExt_eq, hRightStep, hBelow]
    have hChosen : (match (generalizing := false) τ.sideAt J with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
      rw [hSide, hside]
      cases hs : σ.sideAt N
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.u - 1) (σ.k - σ.maximumAt N)).trans (by omega)
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.a - 1) (σ.k - σ.maximumAt N)).trans (by omega)
    have hSmall : min ((match (generalizing := false) τ.sideAt J with | Side.lower => τ.u | Side.upper => τ.a) - 1)
        (τ.k - τ.maximumAt J) ≤ 3 := by
      apply (Nat.min_le_left _ _).trans
      omega
    have hBudget : (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1 = w := by
      dsimp only [τ, w]
      cases hs : σ.sideAt N <;> cases ht : t <;> simp_all only [ne_eq, not_true_eq_false]
    have hBound := ctx_boundary_marker_rank_budget τ hPositive J y hJτ (by rw [hExt]; exact hy)
      inner (by intro p hp; rw [hChild] at hp; exact hInner p hp)
      (by
        intro j hj p hp
        rw [hSide, hBelow] at hj
        rw [hExt] at hp
        exact hInnerYoung j hj p hp)
      t (by rw [hSide, hside]; exact hne) hSmall A B
      (by intro p hp; rw [hChild] at hp; rw [hLeftEq]; exact hLeft p hp)
      (by intro p hp; rw [hChild] at hp; rw [hRightEq]; exact hRight p hp)
    change (∀ fuel, boundFuel fuel τ ≤
        ((match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1) - A - B) ∧
      τ.bound ≤ ((match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1) - A - B at hBound
    rw [hBudget] at hBound
    exact ⟨fun fuel => (hFuel fuel).trans (hBound.1 fuel), hFull.trans hBound.2⟩

  classical
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 2 * w - 1) ∧ α.bound + β.bound ≤ 2 * w - 1
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hQα : q₀ ∈ α.extPositions 1 := (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPositivePart (ks : List ℕ) (v : Side) (q₀ : ℕ) :
      ∀ p j z, (σ.part ks v q₀).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v q₀)
        (show (σ.part ks v q₀).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v q₀ hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v q₀ hpl he] at hp
      cases hp; omega
  have hPosα := hPositivePart rest s m
  have hPosβ := hPositivePart keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
  have hw : 1 ≤ w := hwidth
  have hMpos := one_le_of_mem_levels hM
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMsα : α.sideAt (M + 1) = s := (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ keep t n hMpos).trans hMs
  have hYα : y ∈ α.extPositions (M + 1) := by rw [part_extPositions_succ σ rest s m hMpos]; exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by rw [part_extPositions_succ σ keep t n hMpos]; exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j) (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hBetaActual : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
    rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hBetaBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hAlphaActual : ∀ j ∈ α.levelsOn s 0, ∀ p ∈ α.extPositions j,
      (j = 1 ∧ p ∈ keep) ∨ (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    intro j hj p hp
    rw [part_levelsOn_self_zero hSideα] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Or.inl ⟨rfl, ((hExtα p).mp hp).2⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
      rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hAlphaBelow (top j : ℕ) (hj : j ∈ α.levelsOn s top) :
      j ∈ α.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  obtain ⟨direction, hBoundary, hOrder⟩ : ∃ direction : Bool,
      (∀ p ∈ keep, (if direction then x < p else p < x) ∧
        (if direction then p < y else y < p)) ∧
      (if direction then x < y else y < x) := by
    rcases hbetween with hh | hh
    · have hq := hh q₀ hq₀
      exact ⟨true, hh, by change x < y; omega⟩
    · have hq := hh q₀ hq₀
      exact ⟨false, (by intro p hp; exact ⟨(hh p hp).2, (hh p hp).1⟩), by change y < x; omega⟩
  have hBeforeN : ∀ j ∈ α.levelsOn s (N + 1), ∀ p ∈ α.extPositions j,
      if direction then x < p else p < x := by
    intro j hj p hp
    have hj' := hAlphaBelow (N + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨_, hpk⟩ | ⟨hjN, _⟩ | ⟨hjM, _⟩
    · exact (hBoundary p hpk).1
    · omega
    · omega
  have hBeforeM : ∀ j ∈ α.levelsOn s (M + 1), ∀ p ∈ α.extPositions j,
      if direction then p < y else y < p := by
    intro j hj p hp
    have hj' := hAlphaBelow (M + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨_, hpk⟩ | ⟨_, rfl⟩ | ⟨hjM, _⟩
    · exact (hBoundary p hpk).2
    · exact hOrder
    · omega
  obtain ⟨endpoint, hEnd⟩ : ∃ endpoint : Bool,
      ∀ p ∈ keep, ∀ q ∈ rest, if endpoint then q < p else p < q := by
    rcases hendpoint with hh | hh
    · exact ⟨true, fun p hp q hq => hh p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
    · exact ⟨false, fun p hp q hq => hh p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
  have hChildBoundary : ∀ p ∈ α.childPositions, if endpoint then p < q₀ else q₀ < p := by
    intro p hp
    exact hEnd q₀ hq₀ p ((hChildα p).mp hp)
  have hOwn : (∀ fuel, boundFuel fuel α ≤ w) ∧ α.bound ≤ w := by
    have hLocal (L z : ℕ) (hL : L ∈ α.levels) (h1L : 1 < L)
        (hLs : α.sideAt L = s) (hz : z ∈ α.extPositions L)
        (ho : if endpoint then q₀ < z else z < q₀)
        (hy : ∀ j ∈ α.levelsOn s L, ∀ p ∈ α.extPositions j,
          if endpoint then p < z else z < p) :
        (∀ fuel, boundFuel fuel α ≤ w) ∧ α.bound ≤ w := by
      have hc : ∀ p ∈ α.childPositions, if endpoint then p < z else z < p := by
        intro p hp
        have hh := hChildBoundary p hp
        cases endpoint
        · change z < p
          have h1 : q₀ < p := hh
          have h2 : z < q₀ := ho
          omega
        · change p < z
          have h1 : p < q₀ := hh
          have h2 : q₀ < z := ho
          omega
      have hh := ctx_nested_boundary_markers_rank_budget α hPosα L 1 z q₀ hL hOneα h1L hz hQα
        (by rw [hSideα, hLs]) endpoint endpoint hc (by rw [hLs]; exact hy)
        hChildBoundary (by rw [hSideα]; simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
        t (by rw [hLs]; exact hne) (by rw [hLs]; exact hglobal) 0 0
        (by intro p hp; exact Nat.zero_le _) (by intro p hp; exact Nat.zero_le _)
      exact hh
    have hQ := hBoundary q₀ hq₀
    cases hd : direction <;> cases he : endpoint
    · exact hLocal (M + 1) y hMα (by omega) hMsα hYα
        (by simpa [hd, he] using hQ.2)
        (by intro j hj p hp; simpa [hd, he] using hBeforeM j hj p hp)
    · exact hLocal (N + 1) x hNα (by omega) hNsα hXα
        (by simpa [hd, he] using hQ.1)
        (by intro j hj p hp; simpa [hd, he] using hBeforeN j hj p hp)
    · exact hLocal (N + 1) x hNα (by omega) hNsα hXα
        (by simpa [hd, he] using hQ.1)
        (by intro j hj p hp; simpa [hd, he] using hBeforeN j hj p hp)
    · exact hLocal (M + 1) y hMα (by omega) hMsα hYα
        (by simpa [hd, he] using hQ.2)
        (by intro j hj p hp; simpa [hd, he] using hBeforeM j hj p hp)
  have hOuter : ∀ p ∈ β.childPositions, if direction then p < y else y < p := by
    intro p hp
    exact (hBoundary p ((hChildβ p).mp hp).2).2
  have hInner : ∀ p ∈ β.childPositions, if !direction then p < x else x < p := by
    intro p hp
    have hh := (hBoundary p ((hChildβ p).mp hp).2).1
    cases direction <;> simpa using hh
  have hOuterYoung : ∀ j ∈ β.levelsOn (β.sideAt (M + 1)) (M + 1),
      ∀ p ∈ β.extPositions j, if direction then p < y else y < p := by
    intro j hj p hp
    rw [hMsβ] at hj
    have hj' := hBetaBelow (M + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨_, rfl⟩ | ⟨hjM, _⟩
    · exact hOrder
    · omega
  have hInnerYoung : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (N + 1),
      ∀ p ∈ β.extPositions j, if !direction then p < x else x < p := by
    intro j hj p hp
    rw [hNsβ] at hj
    have hj' := hBetaBelow (N + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨hjN, _⟩ | ⟨hjM, _⟩ <;> omega
  have hOneLeftTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRightTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hOneOn : 1 ∈ β.levelsOn t (N + 1) := List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]; omega⟩
  have hLeft : ∀ p ∈ β.childPositions, (if endpoint then 1 else 0) ≤ β.leftExt t (N + 1) p := by
    intro p hp
    cases he : endpoint
    · simp [he]
    · have hh := hEnd p ((hChildβ p).mp hp).2 l ((hRest l).mpr ⟨hl, hlnot⟩)
      have hlp : l < p := by simpa [he] using hh
      simpa [he] using hOneLeftTop β t (N + 1) 1 p l hOneOn hLβ hlp
  have hRight : ∀ p ∈ β.childPositions, (if endpoint then 0 else 1) ≤ β.rightExt t (N + 1) p := by
    intro p hp
    cases he : endpoint
    · have hh := hEnd p ((hChildβ p).mp hp).2 l ((hRest l).mpr ⟨hl, hlnot⟩)
      have hpl : p < l := by simpa [he] using hh
      simpa [he] using hOneRightTop β t (N + 1) 1 p l hOneOn hLβ hpl
    · simp [he]
  have hGlobalβ : (match (generalizing := false) β.sideAt (M + 1) with | Side.lower => β.u | Side.upper => β.a) ≤ 5 := by
    rw [hMsβ]
    exact hglobal
  have hOther : (∀ fuel, boundFuel fuel β ≤ w - 1) ∧ β.bound ≤ w - 1 := by
    have hh := ctx_nested_boundary_markers_rank_budget β hPosβ (M + 1) (N + 1) y x
      hMβ hNβ (by omega) hYβ hXβ (by rw [hNsβ, hMsβ]) direction (!direction)
      hOuter hOuterYoung hInner hInnerYoung t (by rw [hMsβ]; exact hne) hGlobalβ
      (if endpoint then 1 else 0) (if endpoint then 0 else 1) hLeft hRight
    change (∀ fuel, boundFuel fuel β ≤ w - (if endpoint then 1 else 0) - (if endpoint then 0 else 1)) ∧
      β.bound ≤ w - (if endpoint then 1 else 0) - (if endpoint then 0 else 1) at hh
    cases endpoint <;> simpa using hh
  have hBudget : w + (w - 1) ≤ 2 * w - 1 := by omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOther.2).trans hBudget⟩

end ErdosSzekeres
