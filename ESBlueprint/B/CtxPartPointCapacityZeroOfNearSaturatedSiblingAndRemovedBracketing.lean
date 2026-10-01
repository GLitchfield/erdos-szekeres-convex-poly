import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- In a raw positive-label context, an indexed same-axis sibling maximum at least k-3 forces chosen point capacity zero in any proper part at every position bracketed by two removed source children. Both removed children become fresh level-one markers; their left and right extensions add two to the shifted old join. Arbitrary keep lists, new maxima, history and length; the evaluated position need not itself be a kept child. Restricts active points to exterior removed-child regions in near-saturated maximal-segment exchange.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_point_capacity_zero_of_near_saturated_sibling_and_removed_bracketing (σ : Ctx.Context) (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N : ℕ) (hN : N ∈ σ.levelsOn s 0) (hmaximum : σ.k - 3 ≤ σ.maximumAt N) (keep : List ℕ) (m p r t : ℕ) (hr : r ∈ σ.childPositions) (hremovedr : r ∉ keep) (ht : t ∈ σ.childPositions) (hremovedt : t ∉ keep) (hrp : r < p) (hpt : p < t) : (match s with | Ctx.Side.lower => (σ.part keep s m).cupLimit p p | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0 := by
  classical
  let τ := σ.part keep s m
  have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hN).1
  have hNmem : N ∈ σ.levels := (List.mem_filter.mp hN).1
  have hNside : σ.sideAt N = s := by simpa using (List.mem_filter.mp hN).2
  have hOldMem : N + 1 ∈ τ.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hNmem, rfl⟩)
  have hOldSide : τ.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ keep s m hNpos).trans hNside
  have hOldOn : N + 1 ∈ τ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hOldMem, by simp [hOldSide]⟩
  have hOldMax : τ.maximumAt (N + 1) = σ.maximumAt N :=
    Ctx.Context.part_maximumAt_succ σ keep s m hNpos
  have hrnew : r ∈ τ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simpa using hremovedr⟩
  have htnew : t ∈ τ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨ht, by simpa using hremovedt⟩
  have hFreshSide : τ.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
  have hOne : 1 ∈ τ.levelsOn s (N + 1) := by
    rw [Ctx.Context.part_levelsOn_self_succ hFreshSide hNpos]
    simp
  have hsub : [1].Sublist (τ.levelsOn s (N + 1)) :=
    List.singleton_sublist.mpr hOne
  have hLeft : 1 ≤ τ.leftExt s (N + 1) p := by
    have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
      intro hn
      have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
        List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
      rw [hn] at hm
      cases hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (τ.levelsOn s (N + 1)).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
    change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤
      τ.leftExt s (N + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnon] using hv
  have hRight : 1 ≤ τ.rightExt s (N + 1) p := by
    have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
      intro hn
      have hm : t ∈ (τ.extPositions 1).filter (p < ·) :=
        List.mem_filter.mpr ⟨htnew, by simpa using hpt⟩
      rw [hn] at hm
      cases hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (τ.levelsOn s (N + 1)).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
    change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤
      τ.rightExt s (N + 1) p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnon] using hv
  have hj := Ctx.Context.le_joinExt_of_mem_levelsOn hOldOn p p
  rw [hOldMax] at hj
  have hjoin : σ.k - 1 ≤ τ.joinExt s p p := by
    omega
  have hk : τ.k = σ.k := rfl
  change (match s with
    | Ctx.Side.lower => τ.cupLimit p p
    | Ctx.Side.upper => τ.capLimit p p) = 0
  cases hs : s <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit, hk] <;>
    simp only [hs] at hjoin <;> omega

end ErdosSzekeres
