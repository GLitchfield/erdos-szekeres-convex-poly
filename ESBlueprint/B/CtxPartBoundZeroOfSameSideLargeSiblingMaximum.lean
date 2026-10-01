import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A proper recursive part on the side of an indexed sibling maximum at least k-2 has zero full context bound. One removed child becomes a same-side level-one marker; joining it to the shifted large maximum annihilates every retained chosen-axis point capacity. Positive actual external labels suffice, with arbitrary child runs, unused indexed levels, natural k, keep lists, and new sibling maximum m. Exports the saturation step needed to eliminate zero-capacity branches in the maximal-segment exchange argument.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_point_bases
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_bound_zero_of_same_side_large_sibling_maximum (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (s : Ctx.Side) (N : ℕ) (hN : N ∈ σ.levelsOn s 0)
  (hmaximum : σ.k - 2 ≤ σ.maximumAt N)
  (keep : List ℕ) (m r : ℕ)
  (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
  (σ.part keep s m).bound = 0 := by
  classical
  let lim (ρ : Ctx.Context) (p : ℕ) := match s with
    | Ctx.Side.lower => ρ.cupLimit p p
    | Ctx.Side.upper => ρ.capLimit p p
  have hLevelPart (ρ : Ctx.Context) (keep : List ℕ) (t : Ctx.Side) (m L : ℕ)
      (hL : L ∈ ρ.levelsOn s 0) :
      L + 1 ∈ (ρ.part keep t m).levelsOn s 0 ∧
        (ρ.part keep t m).maximumAt (L + 1) = ρ.maximumAt L := by
    have hmem := (List.mem_filter.mp hL).1
    have h1 := (Ctx.Context.one_le_of_mem_levelsOn hL).1
    have hside : ρ.sideAt L = s := by simpa using (List.mem_filter.mp hL).2
    have hside' : (ρ.part keep t m).sideAt (L + 1) = s :=
      (Ctx.Context.part_sideAt_succ ρ keep t m h1).trans hside
    refine ⟨?_, Ctx.Context.part_maximumAt_succ ρ keep t m h1⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hside']⟩
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hmem, rfl⟩)
  have hKill (ρ : Ctx.Context)
      (hPos : ∀ x l t, ρ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
      (L : ℕ) (hL : L ∈ ρ.levelsOn s 0) (hM : ρ.k - 2 ≤ ρ.maximumAt L)
      (keep : List ℕ) (m r : ℕ) (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep) :
      ∀ p ∈ (ρ.part keep s m).childPositions, lim (ρ.part keep s m) p = 0 := by
    intro p hp
    let τ := ρ.part keep s m
    have hpkeep : p ∈ keep := by
      rw [Ctx.Context.part_childPositions] at hp
      simpa using (List.mem_filter.mp hp).2
    have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [Ctx.Context.part_extPositions_one hPos keep s m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hside : τ.sideAt 1 = s := Ctx.Context.part_sideAt_one_of_mem hPos keep s m hrnew
    have h1 := (Ctx.Context.one_le_of_mem_levelsOn hL).1
    have hone : 1 ∈ τ.levelsOn s (L + 1) := by
      rw [Ctx.Context.part_levelsOn_self_succ hside h1]
      simp
    have hsub : [1].Sublist (τ.levelsOn s (L + 1)) := List.singleton_sublist.mpr hone
    have hExt : 1 ≤ τ.leftExt s (L + 1) p + τ.rightExt s (L + 1) p := by
      by_cases hrp : r < p
      · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤ τ.leftExt s (L + 1) p at hv
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
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤ τ.rightExt s (L + 1) p at hv
        simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
          List.head?_eq_some_head hnon] at hv
        omega
    have hlevel := hLevelPart ρ keep s m L hL
    have hj := Ctx.Context.le_joinExt_of_mem_levelsOn hlevel.1 p p
    rw [hlevel.2] at hj
    have hjoin : ρ.k - 1 ≤ τ.joinExt s p p := by
      change 1 ≤ (ρ.part keep s m).leftExt s (L + 1) p +
        (ρ.part keep s m).rightExt s (L + 1) p at hExt
      change ρ.k - 1 ≤ (ρ.part keep s m).joinExt s p p
      omega
    have hk : τ.k = ρ.k := rfl
    change lim τ p = 0
    cases hs : s <;> simp only [lim, hs, Ctx.Context.cupLimit, Ctx.Context.capLimit, hk] <;>
      simp only [hs] at hjoin <;> omega
  let τ := σ.part keep s m
  have hzero : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0 := by
    intro p hp
    have h := hKill σ hpositive N hN hmaximum keep m r hr hremoved p hp
    cases hs : s with
    | lower => exact Or.inl (by simpa only [lim, τ, hs] using h)
    | upper => exact Or.inr (by simpa only [lim, τ, hs] using h)
  have hsum : (τ.childPositions.map
      (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simp only [Ctx.Context.baseOf, if_pos (hzero p hp)]
  exact Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hsum)

end ErdosSzekeres
