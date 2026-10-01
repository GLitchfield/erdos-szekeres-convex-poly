import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A younger indexed actual marker outside the full source-child span and an older same-axis sibling maximum at least k-3 annihilate every kept point capacity and the full bound after any proper same-side part. The fresh omitted child and younger boundary marker give two extension traces below the older maximum. Raw positive external labels suffice; arbitrary keep duplicates, new maximum, indexed unused levels, history length, globals and child runs are allowed. Supplies an unbounded near-saturation zero mechanism for interior-exchange obstructions.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_point_bases
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_bound_zero_of_near_saturated_sibling_and_younger_boundary_marker (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (J M x : ℕ) (hJ : J ∈ σ.levelsOn s 0) (hM : M ∈ σ.levelsOn s 0) (hJM : J < M) (hx : x ∈ σ.extPositions J) (hboundary : (∀ q ∈ σ.childPositions, x < q) ∨ (∀ q ∈ σ.childPositions, q < x)) (hmaximum : σ.k - 3 ≤ σ.maximumAt M) (keep : List ℕ) (m r : ℕ) (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) : (∀ p ∈ (σ.part keep s m).childPositions, (match s with | Ctx.Side.lower => (σ.part keep s m).cupLimit p p | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0) ∧ (σ.part keep s m).bound = 0 := by
  classical
  let τ := σ.part keep s m
  have hJpos : 1 ≤ J := (Ctx.Context.one_le_of_mem_levelsOn hJ).1
  have hMpos : 1 ≤ M := (Ctx.Context.one_le_of_mem_levelsOn hM).1
  have hJside : σ.sideAt J = s := (of_decide_eq_true (List.mem_filter.mp hJ).2).1
  have hMside : σ.sideAt M = s := (of_decide_eq_true (List.mem_filter.mp hM).2).1
  have hrnew : r ∈ τ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
  have hFreshSide : τ.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
  have hxnew : x ∈ τ.extPositions (J + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ keep s m hJpos]
    exact hx
  have hJbelow : J ∈ σ.levelsOn s M :=
    List.mem_filter.mpr ⟨(List.mem_filter.mp hJ).1, by simp [hJside, hJM]⟩
  have hTwo : [1, J + 1].Sublist (τ.levelsOn s (M + 1)) := by
    rw [Ctx.Context.part_levelsOn_self_succ hFreshSide hMpos]
    exact List.cons_sublist_cons.mpr (List.singleton_sublist.mpr
      (List.mem_map.mpr ⟨J, hJbelow, rfl⟩))
  have hFreshBelow : 1 ∈ τ.levelsOn s (M + 1) := hTwo.subset (by simp)
  have hYoungBelow : J + 1 ∈ τ.levelsOn s (M + 1) := hTwo.subset (by simp)
  have hOldOn : M + 1 ∈ τ.levelsOn s 0 := by
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [Ctx.Context.part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, (List.mem_filter.mp hM).1, rfl⟩)
    · have hside : τ.sideAt (M + 1) = s :=
        (Ctx.Context.part_sideAt_succ σ keep s m hMpos).trans hMside
      simp [hside]
  have hOldMaximum : τ.maximumAt (M + 1) = σ.maximumAt M :=
    Ctx.Context.part_maximumAt_succ σ keep s m hMpos
  have hOneLeft (j p y : ℕ) (hj : j ∈ τ.levelsOn s (M + 1))
      (hy : y ∈ τ.extPositions j) (hyp : y < p) :
      1 ≤ τ.leftExt s (M + 1) p := by
    have hm : y ∈ (τ.extPositions j).filter (· < p) := by simp [hy, hyp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s (M + 1)).sublists.map
      (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ τ.leftExt s (M + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (j p y : ℕ) (hj : j ∈ τ.levelsOn s (M + 1))
      (hy : y ∈ τ.extPositions j) (hpy : p < y) :
      1 ≤ τ.rightExt s (M + 1) p := by
    have hm : y ∈ (τ.extPositions j).filter (p < ·) := by simp [hy, hpy]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s (M + 1)).sublists.map
      (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ τ.rightExt s (M + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hSort : (τ.extPositions 1).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hTwoLeft (p : ℕ) (hrp : r < p) (hxr : x < r) :
      2 ≤ τ.leftExt s (M + 1) p := by
    have hm : r ∈ (τ.extPositions 1).filter (· < p) := by simp [hrnew, hrp]
    have hne := List.ne_nil_of_mem hm
    let y := ((τ.extPositions 1).filter (· < p)).getLast hne
    have hy : ((τ.extPositions 1).filter (· < p)).getLast? = some y :=
      List.getLast?_eq_some_getLast hne
    have hry : r ≤ y := (hSort.filter _).rel_getLast hm
    have hmOld : x ∈ (τ.extPositions (J + 1)).filter (· < y) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hxnew, by omega⟩
    have hneOld := List.ne_nil_of_mem hmOld
    have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s (M + 1)).sublists.map
      (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1, J + 1], List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ τ.leftExt s (M + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep, hy,
      List.getLast?_eq_some_getLast hneOld] using hv
  have hTwoRight (p : ℕ) (hpr : p < r) (hrx : r < x) :
      2 ≤ τ.rightExt s (M + 1) p := by
    have hm : r ∈ (τ.extPositions 1).filter (p < ·) := by simp [hrnew, hpr]
    have hne := List.ne_nil_of_mem hm
    let y := ((τ.extPositions 1).filter (p < ·)).head hne
    have hy : ((τ.extPositions 1).filter (p < ·)).head? = some y :=
      List.head?_eq_some_head hne
    have hyr : y ≤ r := (hSort.filter _).rel_head hm
    have hmOld : x ∈ (τ.extPositions (J + 1)).filter (y < ·) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hxnew, by omega⟩
    have hneOld := List.ne_nil_of_mem hmOld
    have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s (M + 1)).sublists.map
      (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1, J + 1], List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ τ.rightExt s (M + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep, hy,
      List.head?_eq_some_head hneOld] using hv
  have hPoint (p : ℕ) (hp : p ∈ τ.childPositions) :
      (match s with | .lower => τ.cupLimit p p | .upper => τ.capLimit p p) = 0 := by
    have hpSource : p ∈ σ.childPositions := by
      rw [Ctx.Context.part_childPositions] at hp
      exact (List.mem_filter.mp hp).1
    have hpKeep : p ∈ keep := by
      rw [Ctx.Context.part_childPositions] at hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    have hprne : p ≠ r := by intro h; subst p; exact hremoved hpKeep
    have hExt : 2 ≤ τ.leftExt s (M + 1) p + τ.rightExt s (M + 1) p := by
      rcases hboundary with hl | hrB
      · have hxp := hl p hpSource
        have hxr := hl r hr
        by_cases hrp : r < p
        · have ht := hTwoLeft p hrp hxr
          omega
        · have hpr : p < r := by omega
          have hL := hOneLeft (J + 1) p x hYoungBelow hxnew hxp
          have hR := hOneRight 1 p r hFreshBelow hrnew hpr
          omega
      · have hpx := hrB p hpSource
        have hrx := hrB r hr
        by_cases hpr : p < r
        · have ht := hTwoRight p hpr hrx
          omega
        · have hrp : r < p := by omega
          have hL := hOneLeft 1 p r hFreshBelow hrnew hrp
          have hR := hOneRight (J + 1) p x hYoungBelow hxnew hpx
          omega
    have hJoin := Ctx.Context.le_joinExt_of_mem_levelsOn hOldOn p p
    rw [hOldMaximum] at hJoin
    have hStrong : τ.k - 1 ≤ τ.joinExt s p p := by
      change σ.k - 1 ≤ τ.joinExt s p p
      omega
    cases s <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit] <;> omega
  have hSum : (τ.childPositions.map
      (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    have hz := hPoint p hp
    cases s <;> simp only at hz <;> simp [Ctx.Context.baseOf, hz]
  exact ⟨hPoint, Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hSum)⟩

end ErdosSzekeres
