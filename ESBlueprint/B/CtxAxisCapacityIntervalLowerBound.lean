import ESBlueprint.B.CtxNonunitStraddlingCapacityProfile

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An endpoint interpolation lower bound for a chosen point capacity: for p<=r<=q, the sum of the two endpoint capacities is at most the middle capacity plus the chosen global parameter minus one. No positivity, child membership, well-formedness, maximum or history restrictions are needed. Greedy extension monotonicity and cutoff inclusion bound the middle pure-chain and sibling-join constraints by the left endpoint constraints plus the right endpoint left extension; positive right capacity pays that extension. At chosen global at most four, two nonunit endpoints therefore force every intermediate chosen point capacity to be positive. Together with the straddling capacity profile, this determines interior capacity exactly one and rules out hidden chosen-axis zero-capacity gaps in the remaining collision source.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_axis_capacity_interval_lower_bound (σ : Ctx.Context) (s : Ctx.Side) (p r q : ℕ) (hpr : p ≤ r) (hrq : r ≤ q) :
  let global := match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let capacity := fun z => match s with
    | Ctx.Side.lower => σ.cupLimit z z | Ctx.Side.upper => σ.capLimit z z
  capacity p + capacity q ≤ capacity r + (global - 1) := by
  classical
  let G := match s with | Side.lower => σ.u | Side.upper => σ.a
  let C (z : ℕ) := match s with | Side.lower => σ.cupLimit z z | Side.upper => σ.capLimit z z
  change C p + C q ≤ C r + (G - 1)
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
      (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
      (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
    cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
        have hpy : p ≤ y := by
          by_contra h
          have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hx
          exact List.not_mem_nil hx
        simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
    | some x =>
      have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
      have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hb
        rw [hnil] at hxq
        exact False.elim (List.not_mem_nil hxq)
      | some y =>
        have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
          rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
          exact Option.some.inj hb
        have hxy : x ≤ y := by
          simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
        simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
  have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
      (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
      (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
    cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        rw [hnil] at hyp
        exact False.elim (List.not_mem_nil hyp)
    | some x =>
      have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hb
        have hxq : x ≤ q := by
          by_contra h
          have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
          rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
          exact Option.some.inj ha
        have hxy : x ≤ y := by
          simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
        simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
  have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
      (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
      (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepLeft ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
      (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
      (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepRight ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.leftExt v top p ≤ ρ.leftExt v top q := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
  have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.rightExt v top q ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
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
  have hChain : σ.chainExt s r r ≤ σ.chainExt s p p + σ.leftExt s 0 q := by
    have hl := hLeftMono σ s 0 r q hrq
    have hr := hRightMono σ s 0 p r hpr
    simp only [chainExt]
    omega
  have hJoin : σ.joinExt s r r ≤ σ.joinExt s p p + σ.leftExt s 0 q := by
    change max (σ.chainExt s r r)
      ((((σ.levelsOn s 0).map (fun j =>
        σ.leftExt s j r + σ.rightExt s j r + σ.maximumAt j)).max?).getD 0) ≤
          σ.joinExt s p p + σ.leftExt s 0 q
    apply max_le
    · have hh : σ.chainExt s p p ≤ σ.joinExt s p p := Nat.le_max_left _ _
      omega
    · apply getD_max?_le
      intro value hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      have hl := (hLeftCutoff σ s j r).trans (hLeftMono σ s 0 r q hrq)
      have hr := hRightMono σ s j p r hpr
      have hh := le_getD_max?_of_mem
        (L := (σ.levelsOn s 0).map (fun l =>
          σ.leftExt s l p + σ.rightExt s l p + σ.maximumAt l))
        (List.mem_map.mpr ⟨j, hj, rfl⟩)
      have hjp : σ.leftExt s j p + σ.rightExt s j p + σ.maximumAt j ≤ σ.joinExt s p p :=
        hh.trans (Nat.le_max_right _ _)
      omega
  have hPadding : C p ≤ C r + σ.leftExt s 0 q := by
    cases s <;> simp only [C, cupLimit, capLimit] <;> omega
  by_cases hz : C q = 0
  · have hpG : C p ≤ G - 1 := by
      cases s <;> simp only [C, G, cupLimit, capLimit] <;> omega
    omega
  · have hqG : C q + σ.leftExt s 0 q ≤ G - 1 := by
      cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hz ⊢ <;> omega
    omega

end ErdosSzekeres
