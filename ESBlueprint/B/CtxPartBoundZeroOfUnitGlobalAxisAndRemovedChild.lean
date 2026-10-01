import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

/-- A proper part on an axis whose global parameter is at most two has zero selected point capacity at every retained child and zero full recursive bound. One omitted source child supplies an indexed fresh-side marker, forcing a chain extension of at least one. Positive actual external labels suffice, with arbitrary raw words, maxima, k and keep lists. Removes the opposite-side branch in axis-two one-level-root normal-form induction; the selected-path minimum remains a separate obligation.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_point_bases
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_part_bound_zero_of_unit_global_axis_and_removed_child (σ : Ctx.Context)
    (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
    (s : Ctx.Side)
    (hunit : match s with | Ctx.Side.lower => σ.u ≤ 2 | Ctx.Side.upper => σ.a ≤ 2)
    (keep : List ℕ) (m r : ℕ)
    (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
    (∀ p ∈ (σ.part keep s m).childPositions,
      (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0) ∧
      (σ.part keep s m).bound = 0 := by
  classical
  let τ := σ.part keep s m
  have hrnew : r ∈ τ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
  have hside : τ.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
  have hone : 1 ∈ τ.levelsOn s 0 := by
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hside]⟩
    change 1 ∈ (σ.part keep s m).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_self
  have hsub : [1].Sublist (τ.levelsOn s 0) := List.singleton_sublist.mpr hone
  have hzero : ∀ p ∈ τ.childPositions,
      (match s with
      | Ctx.Side.lower => τ.cupLimit p p
      | Ctx.Side.upper => τ.capLimit p p) = 0 := by
    intro p hp
    have hpkeep : p ∈ keep := by
      rw [Ctx.Context.part_childPositions] at hp
      simpa using (List.mem_filter.mp hp).2
    have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
    have hExt : 1 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p := by
      by_cases hrp : r < p
      · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤ τ.leftExt s 0 p at hv
        simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
          List.getLast?_eq_some_getLast hnon] at hv
        omega
      · have hpr : p < r := by omega
        have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤ τ.rightExt s 0 p at hv
        simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
          List.head?_eq_some_head hnon] at hv
        omega
    have hchain : 1 ≤ τ.chainExt s p p := hExt
    cases s with
    | lower =>
      change σ.u ≤ 2 at hunit
      change min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
        (σ.k - 1 - τ.joinExt Ctx.Side.lower p p) = 0
      omega
    | upper =>
      change σ.a ≤ 2 at hunit
      change min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
        (σ.k - 1 - τ.joinExt Ctx.Side.upper p p) = 0
      omega
  have hz : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0 := by
    intro p hp
    have h := hzero p hp
    cases s with
    | lower => exact Or.inl h
    | upper => exact Or.inr h
  have hsum : (τ.childPositions.map
      (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simp only [Ctx.Context.baseOf, if_pos (hz p hp)]
  exact ⟨hzero, Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hsum)⟩

end ErdosSzekeres
