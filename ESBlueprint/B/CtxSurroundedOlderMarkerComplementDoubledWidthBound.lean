import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ESBlueprint.B.CtxNestedBoundaryMarkersRankBudget
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- When the older of two chosen-axis markers lies between two occurrences of the only still-relevant base level and every active child lies outside that interval, split physical child runs at the older marker. After pruning the base level to one boundary occurrence on each arm, nested boundary budgets bound each group by one opposite width, so every fuel approximation and the full recursive bound are at most twice that width. Both marker orders, arbitrary opposite history, maxima, inactive children, and k remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_single_level_occurrence_prune_bound_mono, ErdosSzekeres.ctx_nested_boundary_markers_rank_budget, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_capacity_three, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_surrounded_older_marker_complement_doubled_width_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (J N M a b x y : ℕ) (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hJN : J < N) (hNM : N < M) (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (ha : a ∈ σ.extPositions J) (hb : b ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hay : a < y) (hyb : y < b) (houtside : ∀ p ∈ σ.childPositions, p < a ∨ b < p) (hBeforeN : ∀ j ∈ σ.levelsOn s N, ∀ p ∈ σ.extPositions j, j = J) (hBeforeM : ∀ j ∈ σ.levelsOn s M, ∀ p ∈ σ.extPositions j, j = J ∨ (j = N ∧ p = x)) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * w) ∧ σ.bound ≤ 2 * w := by
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
  let w := (match (generalizing := false) t with
    | Side.lower => σ.u | Side.upper => σ.a) - 1
  let color (p : ℕ) := if p < y then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p =>
      match (generalizing := false) σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ 2 * w) ∧ σ.bound ≤ 2 * w
  have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ y := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hy).2
    simp [hc] at he
  have hMOn : M ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
  have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    intro p hp
    have hn := hNe p hp
    by_cases hpx : p < y
    · have he := hOneRight σ s M p y hMOn hy hpx
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s M p y hMOn hy (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ σ.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < y) = (q < y) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        have hxc := hbetween y (by omega) (by omega)
        exact hNe y hxc rfl
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
  have hSide (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).sideAt j = σ.sideAt j := (hHist c j hj).2
  have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < y := by
    have hh := ((hChild 0 p).mp hp).2
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : y < p := by
    have hh := ((hChild 1 p).mp hp).2
    have hn := hNe p ((hChild 1 p).mp hp).1
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have hLeftChild (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < a := by
    have hh := h0 p hp
    have ho := houtside p ((hChild 0 p).mp hp).1
    omega
  have hRightChild (p : ℕ) (hp : p ∈ (group 1).childPositions) : b < p := by
    have hh := h1 p hp
    have ho := houtside p ((hChild 1 p).mp hp).1
    omega
  have hLinear (c q L z : ℕ) (hq : q ∈ σ.extPositions J)
      (hL : L ∈ σ.levels) (hJL : J < L) (hLs : σ.sideAt L = s)
      (hz : z ∈ σ.extPositions L) (direction : Bool)
      (hBoundary : ∀ p ∈ (group c).childPositions, if direction then p < q else q < p)
      (hqz : if direction then q < z else z < q)
      (hHistory : ∀ j ∈ σ.levelsOn s L, ∀ p ∈ σ.extPositions j,
        j = J ∨ (if direction then p < z else z < p)) : (group c).bound ≤ w := by
    let ρ : Context := { group c with word :=
      (List.range (group c).word.length).map (fun p =>
        match (generalizing := false) (group c).letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = J then
            if p ∈ [q] then Letter.ext J ((group c).sideAt J)
              else Letter.ext ((group c).maxima.length + 1) v
            else Letter.ext j v) }
    have hqG : q ∈ (group c).extPositions J := by
      rw [(hHist c J hJ).1]
      exact hq
    have hp := ctx_single_level_occurrence_prune_bound_mono
      (group c) (hPos c) J hJ [q] q hqG (by simp)
    have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
    have hChildρ : ρ.childPositions = (group c).childPositions := hp.2.1
    have hHistρ : ∀ j ∈ σ.levels, ρ.sideAt j = (group c).sideAt j ∧
        ρ.maximumAt j = (group c).maximumAt j ∧
        ρ.extPositions j = if j = J then ((group c).extPositions j).filter (· ∈ [q])
          else (group c).extPositions j := hp.2.2.1
    have hSideρ (j : ℕ) (hj : j ∈ σ.levels) : ρ.sideAt j = σ.sideAt j :=
      (hHistρ j hj).1.trans (hSide c j hj)
    have hQ : q ∈ ρ.extPositions J := by
      rw [(hHistρ J hJ).2.2, if_pos rfl]
      simp [hqG]
    have hZP : z ∈ ρ.extPositions L := by
      rw [(hHistρ L hL).2.2, if_neg (show L ≠ J by omega), (hHist c L hL).1]
      exact hz
    have hOld (j : ℕ) (hj : j ∈ σ.levels) (p : ℕ)
        (hp : p ∈ ρ.extPositions j) : p ∈ σ.extPositions j := by
      rw [(hHistρ j hj).2.2] at hp
      rw [← (hHist c j hj).1]
      by_cases hjJ : j = J
      · rw [if_pos hjJ] at hp
        exact (List.mem_filter.mp hp).1
      · simpa only [if_neg hjJ] using hp
    have hMemOld (j top : ℕ) (hj : j ∈ ρ.levelsOn s top) :
        j ∈ σ.levelsOn s top := by
      have hjL : j ∈ σ.levels := (List.mem_filter.mp hj).1
      have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨hjL, ?_⟩
      have hs : σ.sideAt j = s := (hSideρ j hjL).symm.trans hjP.1
      simp [hs, hjP.2]
    have hOuter : ∀ p ∈ ρ.childPositions, if direction then p < z else z < p := by
      intro p hp
      rw [hChildρ] at hp
      have hh := hBoundary p hp
      cases direction
      · change z < p
        have hqp : q < p := hh
        have hxq : z < q := hqz
        omega
      · change p < z
        have hpq : p < q := hh
        have hqx' : q < z := hqz
        omega
    have hOuterYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L,
        ∀ p ∈ ρ.extPositions j, if direction then p < z else z < p := by
      intro j hj p hp
      rw [hSideρ L hL, hLs] at hj
      have hjL : j ∈ σ.levels := (List.mem_filter.mp hj).1
      rcases hHistory j (hMemOld j L hj) p (hOld j hjL p hp) with hjJ | hpos
      · rw [(hHistρ j hjL).2.2, if_pos hjJ] at hp
        have hpq := List.mem_singleton.mp (of_decide_eq_true (List.mem_filter.mp hp).2)
        rw [hpq]
        exact hqz
      · exact hpos
    have hInnerYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt J) J,
        ∀ p ∈ ρ.extPositions j, if direction then p < q else q < p := by
      intro j hj p hp
      have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
      have hJpos := one_le_of_mem_levels hJ
      have hjN : j ∈ ρ.levelsOn s N := by
        apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        have hs : ρ.sideAt j = s := hjP.1.trans ((hSideρ J hJ).trans hJs)
        simp [hs]
        omega
      have hh := hBeforeN j (hMemOld j N hjN) p
        (hOld j (List.mem_filter.mp hjN).1 p hp)
      omega
    have hh := ctx_nested_boundary_markers_rank_budget ρ hPosρ
      L J z q hL hJ hJL hZP hQ
      (by rw [hSideρ J hJ, hSideρ L hL, hJs, hLs]) direction direction
      hOuter hOuterYoung
      (by intro p hp; rw [hChildρ] at hp; exact hBoundary p hp)
      hInnerYoung t (by rw [hSideρ L hL, hLs]; exact hne)
      (by rw [hSideρ L hL, hLs]; exact hglobal) 0 0
      (by intro p hp; exact Nat.zero_le _) (by intro p hp; exact Nat.zero_le _)
    have hFull : (group c).bound ≤ ρ.bound := hp.2.2.2.2.2.2
    exact hFull.trans hh.2
  have hXY : x ≠ y := by
    intro he
    subst y
    have hx' := (List.mem_filter.mp hx).2
    have hy' := (List.mem_filter.mp hy).2
    cases hh : σ.letterAt x <;> simp [hh] at hx' hy'
    omega
  have hSum : (group 0).bound + (group 1).bound ≤ 2 * w := by
    by_cases hxy : x < y
    · have hLeft := hLinear 0 a M y ha hM (by omega) hMs hy true
        hLeftChild hay
        (by
          intro j hj p hp
          rcases hBeforeM j hj p hp with hjJ | ⟨_, hpx⟩
          · exact Or.inl hjJ
          · right; change p < y; omega)
      have hRight := hLinear 1 b N x hb hN hJN hNs hx false
        hRightChild (by change x < b; omega)
        (by intro j hj p hp; exact Or.inl (hBeforeN j hj p hp))
      omega
    · have hyx : y < x := by omega
      have hLeft := hLinear 0 a N x ha hN hJN hNs hx true
        hLeftChild (by change a < x; omega)
        (by intro j hj p hp; exact Or.inl (hBeforeN j hj p hp))
      have hRight := hLinear 1 b M y hb hM (by omega) hMs hy false
        hRightChild hyb
        (by
          intro j hj p hp
          rcases hBeforeM j hj p hp with hjJ | ⟨_, hpx⟩
          · exact Or.inl hjJ
          · right; change y < p; omega)
      omega
  have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive
    color ({0, 1} : Finset ℕ) hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
    σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hBudget : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤ 2 * w := by
    simpa using hSum
  exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

end ErdosSzekeres
