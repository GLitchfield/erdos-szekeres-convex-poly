import ESBlueprint.B.CtxNestedBoundaryMarkersRankBudget
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Three ordered chosen-axis markers with empty chosen history below the oldest marker and opposite-facing history constraints around the two younger markers force a doubled opposite-width bound. Splitting active child runs at the oldest marker yields two pruned groups, each bounded by one opposite width through nested boundary markers; capacity-three recombination gives both every fuel approximation and the full recursive bound at most twice that width. Arbitrary opposite history, maxima, and inactive children remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_nested_boundary_markers_rank_budget, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_capacity_three, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_youngest_middle_marker_doubled_width_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (J N M x y z : ℕ) (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hJN : J < N) (hNM : N < M) (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions J) (hy : y ∈ σ.extPositions N) (hz : z ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hyoung : ∀ j ∈ σ.levelsOn s J, σ.extPositions j = []) (direction : Bool) (hBeforeN : ∀ j ∈ σ.levelsOn s N, ∀ p ∈ σ.extPositions j, if direction then y < p else p < y) (hBeforeM : ∀ j ∈ σ.levelsOn s M, ∀ p ∈ σ.extPositions j, if direction then p < z else z < p) : let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * w) ∧ σ.bound ≤ 2 * w := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let color (p : ℕ) := if p < x then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ 2 * w) ∧ σ.bound ≤ 2 * w
  have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp [hc] at he
  have hJOn : J ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hJ, by simp [hJs]⟩
  have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    intro p hp
    have hn := hNe p hp
    by_cases hpx : p < x
    · have he := hOneRight σ s J p x hJOn hx hpx
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s J p x hJOn hx (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ σ.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < x) = (q < x) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        have hxc := hbetween x (by omega) (by omega)
        exact hNe x hxc rfl
      · omega
    simp only [color, hside]
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧
        (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) :
      (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
  have hX (c : ℕ) : x ∈ (group c).extPositions J := by
    rw [(hHist c J hJ).1]
    exact hx
  have hY (c : ℕ) : y ∈ (group c).extPositions N := by
    rw [(hHist c N hN).1]
    exact hy
  have hZ (c : ℕ) : z ∈ (group c).extPositions M := by
    rw [(hHist c M hM).1]
    exact hz
  have hSide (c : ℕ) : (group c).sideAt J = s := (hHist c J hJ).2.trans hJs
  have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < x := by
    have hh := ((hChild 0 p).mp hp).2
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : x < p := by
    have hh := ((hChild 1 p).mp hp).2
    have hn := hNe p ((hChild 1 p).mp hp).1
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have hJBelowN : J ∈ σ.levelsOn s N :=
    List.mem_filter.mpr ⟨hJ, by simp [hJs, hJN]⟩
  have hJBelowM : J ∈ σ.levelsOn s M :=
    List.mem_filter.mpr ⟨hJ, by simp [hJs]; omega⟩
  have hBetweenN := hBeforeN J hJBelowN x hx
  have hBetweenM := hBeforeM J hJBelowM x hx
  have hGroupBound (c L b : ℕ) (hL : L ∈ σ.levels) (hJL : J < L)
      (hLs : σ.sideAt L = s) (hb : b ∈ σ.extPositions L)
      (outer inner : Bool)
      (hOuter : ∀ p ∈ (group c).childPositions, if outer then p < b else b < p)
      (hInner : ∀ p ∈ (group c).childPositions, if inner then p < x else x < p)
      (hHistory : ∀ j ∈ σ.levelsOn s L, ∀ p ∈ σ.extPositions j,
        if outer then p < b else b < p) : (group c).bound ≤ w := by
    have hLside : (group c).sideAt L = s := (hHist c L hL).2.trans hLs
    have hB : b ∈ (group c).extPositions L := by
      rw [(hHist c L hL).1]
      exact hb
    have hGlobal : (match (group c).sideAt L with
        | Side.lower => (group c).u | Side.upper => (group c).a) ≤ 5 := by
      rw [hLside]
      exact hglobal
    have hh := ctx_nested_boundary_markers_rank_budget (group c) (hPos c)
      L J b x hL hJ hJL hB (hX c) (by rw [hSide c, hLside]) outer inner hOuter
      (by
        intro j hj p hp
        rw [hLside, hLevels c s L] at hj
        rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
        exact hHistory j hj p hp)
      hInner
      (by
        intro j hj p hp
        rw [hSide c, hLevels c s J] at hj
        rw [(hHist c j (List.mem_filter.mp hj).1).1, hyoung j hj] at hp
        exact False.elim (List.not_mem_nil hp))
      t (by rw [hLside]; exact hne) hGlobal 0 0
      (by intro p hp; exact Nat.zero_le _) (by intro p hp; exact Nat.zero_le _)
    exact hh.2
  have hSum : (group 0).bound + (group 1).bound ≤ 2 * w := by
    cases hd : direction
    · have hxy : x < y := by simpa [hd] using hBetweenN
      have hzx : z < x := by simpa [hd] using hBetweenM
      have hA := hGroupBound 0 N y hN hJN hNs hy true true
        (by intro p hp; have hh := h0 p hp; simp only [Bool.true_eq, ite_true]; omega) h0
        (by intro j hj p hp; simpa [hd] using hBeforeN j hj p hp)
      have hB := hGroupBound 1 M z hM (by omega) hMs hz false false
        (by intro p hp; have hh := h1 p hp; simp only [Bool.false_eq_true, ite_false]; omega) h1
        (by intro j hj p hp; simpa [hd] using hBeforeM j hj p hp)
      omega
    · have hyx : y < x := by simpa [hd] using hBetweenN
      have hxz : x < z := by simpa [hd] using hBetweenM
      have hA := hGroupBound 0 M z hM (by omega) hMs hz true true
        (by intro p hp; have hh := h0 p hp; simp only [Bool.true_eq, ite_true]; omega) h0
        (by intro j hj p hp; simpa [hd] using hBeforeM j hj p hp)
      have hB := hGroupBound 1 N y hN hJN hNs hy false false
        (by intro p hp; have hh := h1 p hp; simp only [Bool.false_eq_true, ite_false]; omega) h1
        (by intro j hj p hp; simpa [hd] using hBeforeN j hj p hp)
      omega
  have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive
    color ({0, 1} : Finset ℕ) hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
    σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hBudget : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤ 2 * w := by
    simpa using hSum
  exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

end ErdosSzekeres
