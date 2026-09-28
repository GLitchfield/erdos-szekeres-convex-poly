import ESBlueprint.B.CtxBoundaryMarkerRankBudget
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Split at the younger chosen marker into nested linear and boundary-pair arms. Uniform opposite extension losses A and B below the younger level give reduced width v=w-A-B and bound choose(v+1,2)+v. The zero-loss case is one above the sharp bare potential, while nonzero losses remove unnecessary recursion in surrounding cuts. Positive external labels, chosen global at most five, and two actual indexed chosen positions at levels N<M containing all actual chosen positions. Every child has opposite left extension at least A and right extension at least B below the younger chosen level N. Arbitrary opposite history, maxima, inactive children and nonnegative reduced widths are allowed. No recursive potential premise. The zero-loss conclusion is the coarse bound choose(w+1,2)+w; the sharp bare potential remains unproved.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_triangular_linear_rank_budget (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (A B : ℕ)
  (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t N p)
  (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t N p) :
  let v := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (v + 1).choose 2 + v) ∧
    σ.bound ≤ (v + 1).choose 2 + v := by
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
  let v := w - A - B
  let β := σ
  change (∀ fuel, boundFuel fuel σ ≤ (v + 1).choose 2 + v) ∧ σ.bound ≤ (v + 1).choose 2 + v
  have hNpos := one_le_of_mem_levels hN
  have hMpos := one_le_of_mem_levels hM
  have hPosβ := hpositive
  have hNβ : N ∈ β.levels := hN
  have hMβ : M ∈ β.levels := hM
  have hNsβ : β.sideAt N = s := hNs
  have hMsβ : β.sideAt M = s := hMs
  have hXβ : x ∈ β.extPositions N := hx
  have hYβ : y ∈ β.extPositions M := hy
  have hChildNe (ρ : Context) (p j z : ℕ) (hp : p ∈ ρ.childPositions)
      (hz : z ∈ ρ.extPositions j) : p ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j)
      (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases he : σ.letterAt p <;> simp [he] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hActualβ : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := hActual
  have hBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hNoX (p : ℕ) (hp : p ∈ β.childPositions) : p ≠ x :=
    hChildNe β p N x hp hXβ
  have hNoY (p : ℕ) (hp : p ∈ β.childPositions) : p ≠ y :=
    hChildNe β p M y hp hYβ
  have hOneLeft (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let color (p : ℕ) := if p < x then (0 : ℕ) else 1
  let support (c : ℕ) := β.childPositions.filter (fun p ↦ color p = c)
  let group (c : ℕ) : Context := { β with
    word := (List.range β.word.length).map (fun p ↦ match β.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (β.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  have hSmall : ∀ p ∈ β.childPositions, min (β.cupLimit p p) (β.capLimit p p) ≤ 3 := by
    intro p hp
    have hOn : N ∈ β.levelsOn s 0 := List.mem_filter.mpr ⟨hNβ, by simp [hNsβ]⟩
    by_cases hh : p < x
    · have he := hOneRight β s 0 N p x hOn hXβ hh
      cases s <;> simp only [β, part, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
    · have he := hOneLeft β s 0 N p x hOn hXβ (by have := hNoX p hp; omega)
      cases s <;> simp only [β, part, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
  have hCover : ∀ p ∈ β.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ β.childPositions, ∀ q ∈ β.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ β.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < x) = (q < x) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        exact hNoX x (hbetween x (by omega) (by omega)) rfl
      · omega
    simp only [color, hside]
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ β.childPositions ∧ color p = c := by
    have hh : (group c).childPositions = β.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ β.levels) :
      (group c).extPositions j = β.extPositions j ∧ (group c).sideAt j = β.sideAt j :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) :
      (group c).levelsOn v top = β.levelsOn v top :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.2.2.1 v top
  have hSideN (c : ℕ) : (group c).sideAt N = s := (hHist c _ hNβ).2.trans hNsβ
  have hSideM (c : ℕ) : (group c).sideAt M = s := (hHist c _ hMβ).2.trans hMsβ
  have hX (c : ℕ) : x ∈ (group c).extPositions N := by
    rw [(hHist c _ hNβ).1]; exact hXβ
  have hY (c : ℕ) : y ∈ (group c).extPositions M := by
    rw [(hHist c _ hMβ).1]; exact hYβ
  have hBefore (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < x := by
    have hc := ((hChild 0 p).mp hp).2
    dsimp only [color] at hc
    split_ifs at hc <;> omega
  have hAfter (p : ℕ) (hp : p ∈ (group 1).childPositions) : x < p := by
    have hc := ((hChild 1 p).mp hp).2
    have hpne := hNoX p ((hChild 1 p).mp hp).1
    dsimp only [color] at hc
    split_ifs at hc <;> omega
  have hYoung (c j : ℕ) (hj : j ∈ (group c).levelsOn s N)
      (p : ℕ) (hp : p ∈ (group c).extPositions j) : False := by
    rw [hLevels] at hj
    have hj' := hBelow N j hj
    rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
    rcases hActualβ j hj'.1 p hp with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega
  have hOlder (c j : ℕ) (hj : j ∈ (group c).levelsOn s M)
      (p : ℕ) (hp : p ∈ (group c).extPositions j) : p = x := by
    rw [hLevels] at hj
    have hj' := hBelow M j hj
    rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
    rcases hActualβ j hj'.1 p hp with ⟨_, hpx⟩ | ⟨hjM, _⟩
    · exact hpx
    · omega
  have hCutoff (ρ : Context) (v : Side) (top : ℕ) :
      (ρ.levelsOn v top).Sublist (ρ.levelsOn v 0) := by
    have he : ρ.levelsOn v top =
        (ρ.levelsOn v 0).filter (fun j => decide (top = 0 ∨ j < top)) := by
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp [Bool.and_comm]
    rw [he]
    exact List.filter_sublist
  have hLeftCutoff (ρ : Context) (v : Side) (top z : ℕ) :
      ρ.leftExt v top z ≤ ρ.leftExt v 0 z := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ v top)), rfl⟩, le_rfl⟩
  have hRightCutoff (ρ : Context) (v : Side) (top z : ℕ) :
      ρ.rightExt v top z ≤ ρ.rightExt v 0 z := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ v top)), rfl⟩, le_rfl⟩
  have hTrace (c : ℕ) (v : Side) (top p : ℕ) :
      (group c).leftExt v top p = β.leftExt v top p ∧
        (group c).rightExt v top p = β.rightExt v top p :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.2.2.2.1 v top p
  have hLeftGroup (c p : ℕ) (hp : p ∈ (group c).childPositions) :
      A ≤ (group c).leftExt t N p := by
    rw [(hTrace c t N p).1]
    exact hLeft p ((hChild c p).mp hp).1
  have hRightGroup (c p : ℕ) (hp : p ∈ (group c).childPositions) :
      B ≤ (group c).rightExt t N p := by
    rw [(hTrace c t N p).2]
    exact hRight p ((hChild c p).mp hp).1
  have hLeftGroupFull (c p : ℕ) (hp : p ∈ (group c).childPositions) :
      A ≤ (group c).leftExt t 0 p :=
    (hLeftGroup c p hp).trans (hLeftCutoff (group c) t N p)
  have hRightGroupFull (c p : ℕ) (hp : p ∈ (group c).childPositions) :
      B ≤ (group c).rightExt t 0 p :=
    (hRightGroup c p hp).trans (hRightCutoff (group c) t N p)
  have hPairBound (ρ : Context)
      (hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (J z : ℕ) (hJ : J ∈ ρ.levels) (hJs : ρ.sideAt J = s)
      (hz : z ∈ ρ.extPositions J) (direction : Bool)
      (hChildren : ∀ p ∈ ρ.childPositions, if direction then p < z else z < p)
      (hYounger : ∀ j ∈ ρ.levelsOn s J, ∀ p ∈ ρ.extPositions j,
        if direction then p < z else z < p)
      (hG : (match (generalizing := false) s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5)
      (hW : (match (generalizing := false) t with | Side.lower => ρ.u | Side.upper => ρ.a) - 1 = w)
      (hL : ∀ p ∈ ρ.childPositions, A ≤ ρ.leftExt t 0 p)
      (hR : ∀ p ∈ ρ.childPositions, B ≤ ρ.rightExt t 0 p) :
      ρ.bound ≤ (v + 1).choose 2 := by
    let active := ρ.childPositions.toFinset.filter
      (fun p ↦ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (ρ.leftExt t 0 p + 1) (w - ρ.rightExt t 0 p)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z ↦ z.1 ≤ z.2)
    let pairs := active.biUnion (fun p ↦ Q (I p))
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ ↦ Sym2.mk z.1 z.2)
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
          · exact ⟨(b, a), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
    have hSmallG : min ((match (generalizing := false) ρ.sideAt J with
        | Side.lower => ρ.u | Side.upper => ρ.a) - 1) (ρ.k - ρ.maximumAt J) ≤ 4 := by
      rw [hJs]
      apply (Nat.min_le_left _ _).trans
      omega
    have hh := ctx_active_boundary_marker_rank_pair_union_bound ρ hPosρ J z hJ hz
      direction (fun p hp _ ↦ hChildren p hp) (by rw [hJs]; exact hYounger)
      t (by rw [hJs]; exact hne) hSmallG
    have hPairFull : ρ.bound ≤ pairs.card := by
      cases t <;> simpa only [pairs, active, Q, I, hW] using hh.2
    have hsub : pairs ⊆ Q (Finset.Icc (A + 1) (w - B)) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hc := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hL' := hL p hc
      have hR' := hR p hc
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
      have hza' := Finset.mem_Icc.mp hza
      have hzb' := Finset.mem_Icc.mp hzb
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
         Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hz'.2⟩
    have hi : (Finset.Icc (A + 1) (w - B)).card = v := by
      dsimp only [v]
      rw [Nat.card_Icc]
      omega
    have hc : (Q (Finset.Icc (A + 1) (w - B))).card = (v + 1).choose 2 := by
      rw [hCardPairs, hi]
    exact hPairFull.trans ((Finset.card_le_card hsub).trans_eq hc)
  have hXY : x ≠ y := by
    intro he
    have hh := hAtLevel N M x hx (by simpa only [he] using hy)
    omega
  have hSum : (group 0).bound + (group 1).bound ≤ v + (v + 1).choose 2 := by
    by_cases hxy : x < y
    · have hFar := ctx_nested_boundary_markers_rank_budget (group 0) (hPos 0)
        M N y x hMβ hNβ hNM (hY 0) (hX 0)
        (by rw [hSideN, hSideM]) true true
        (fun p hp ↦ lt_trans (hBefore p hp) hxy)
        (by
          rw [hSideM]
          intro j hj p hp
          have he := hOlder 0 j hj p hp
          change p < y
          omega)
        hBefore
        (by rw [hSideN]; intro j hj p hp; exact False.elim (hYoung 0 j hj p hp))
        t (by rw [hSideM]; exact hne) (by rw [hSideM]; exact hglobal)
        A B (hLeftGroup 0) (hRightGroup 0)
      have hFarBound : (group 0).bound ≤ v := by simpa using hFar.2
      have hNear : (group 1).bound ≤ (v + 1).choose 2 :=
        hPairBound (group 1) (hPos 1) N x hNβ (hSideN 1) (hX 1) false hAfter
          (fun j hj p hp ↦ False.elim (hYoung 1 j hj p hp)) hglobal rfl (hLeftGroupFull 1) (hRightGroupFull 1)
      omega
    · have hyx : y < x := by omega
      have hFar := ctx_nested_boundary_markers_rank_budget (group 1) (hPos 1)
        M N y x hMβ hNβ hNM (hY 1) (hX 1)
        (by rw [hSideN, hSideM]) false false
        (fun p hp ↦ lt_trans hyx (hAfter p hp))
        (by
          rw [hSideM]
          intro j hj p hp
          have he := hOlder 1 j hj p hp
          change y < p
          omega)
        hAfter
        (by rw [hSideN]; intro j hj p hp; exact False.elim (hYoung 1 j hj p hp))
        t (by rw [hSideM]; exact hne) (by rw [hSideM]; exact hglobal)
        A B (hLeftGroup 1) (hRightGroup 1)
      have hFarBound : (group 1).bound ≤ v := by simpa using hFar.2
      have hNear : (group 0).bound ≤ (v + 1).choose 2 :=
        hPairBound (group 0) (hPos 0) N x hNβ (hSideN 0) (hX 0) true hBefore
          (fun j hj p hp ↦ False.elim (hYoung 0 j hj p hp)) hglobal rfl (hLeftGroupFull 0) (hRightGroupFull 0)
      omega
  have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three β hPosβ color
    ({0, 1} : Finset ℕ) hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound)) ∧
    σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound) at hDecomp
  have hSum' : ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound) ≤
      (v + 1).choose 2 + v := by simpa [Nat.add_comm] using hSum
  exact ⟨fun f ↦ (hDecomp.1 f).trans hSum', hDecomp.2.trans hSum'⟩

end ErdosSzekeres
