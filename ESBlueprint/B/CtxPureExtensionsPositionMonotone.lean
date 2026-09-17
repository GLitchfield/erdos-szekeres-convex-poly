import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- Pure extension counts are monotone in physical position: moving a point right cannot decrease the maximal left pure-extension length and cannot increase the maximal right pure-extension length, at every side and history cutoff. This exports a fold monotonicity fact previously reproved locally in multiple rank-potential modules and supports cross-combining marker-separated collision intervals.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_pure_extensions_position_monotone (σ : Ctx.Context) (v : Ctx.Side) (top p q : ℕ) (hpq : p ≤ q) : σ.leftExt v top p ≤ σ.leftExt v top q ∧ σ.rightExt v top q ≤ σ.rightExt v top p := by
  classical
  open Ctx Ctx.Context in
    have hSort (j : ℕ) : (σ.extPositions j).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hStepLeft (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
        (leftStep σ (p, c) j).1 ≤ (leftStep σ (q, d) j).1 ∧
        (leftStep σ (p, c) j).2 ≤ (leftStep σ (q, d) j).2 := by
      cases ha : ((σ.extPositions j).filter (· < p)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp ha
        cases hb : ((σ.extPositions j).filter (· < q)).getLast? with
        | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
        | some y =>
          have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
          have hpy : p ≤ y := by
            by_contra h
            have hx : y ∈ (σ.extPositions j).filter (· < p) :=
              List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1,
                by simp only [decide_eq_true_eq]; omega⟩
            rw [hnil] at hx
            exact List.not_mem_nil hx
          simpa only [leftStep, ha, hb] using
            And.intro hpy (show c ≤ d + 1 by omega)
      | some x =>
        have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
        have hxq : x ∈ (σ.extPositions j).filter (· < q) := by
          have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1,
            by simp only [decide_eq_true_eq]; omega⟩
        cases hb : ((σ.extPositions j).filter (· < q)).getLast? with
        | none =>
          have hnil := List.getLast?_eq_none_iff.mp hb
          rw [hnil] at hxq
          exact False.elim (List.not_mem_nil hxq)
        | some y =>
          have hlast : ((σ.extPositions j).filter (· < q)).getLast
              (List.ne_nil_of_mem hxq) = y := by
            rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
            exact Option.some.inj hb
          have hxy : x ≤ y := by
            simpa only [hlast] using ((hSort j).filter _).rel_getLast hxq
          simpa only [leftStep, ha, hb] using
            And.intro hxy (show c + 1 ≤ d + 1 by omega)
    have hStepRight (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
        (rightStep σ (p, c) j).1 ≤ (rightStep σ (q, d) j).1 ∧
        (rightStep σ (q, d) j).2 ≤ (rightStep σ (p, c) j).2 := by
      cases ha : ((σ.extPositions j).filter (p < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp ha
        cases hb : ((σ.extPositions j).filter (q < ·)).head? with
        | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
          have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyp : y ∈ (σ.extPositions j).filter (p < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1,
              by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hyp
          exact False.elim (List.not_mem_nil hyp)
      | some x =>
        have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
        cases hb : ((σ.extPositions j).filter (q < ·)).head? with
        | none =>
          have hnil := List.head?_eq_none_iff.mp hb
          have hxq : x ≤ q := by
            by_contra h
            have hmem : x ∈ (σ.extPositions j).filter (q < ·) :=
              List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1,
                by simp only [decide_eq_true_eq]; omega⟩
            rw [hnil] at hmem
            exact List.not_mem_nil hmem
          simpa only [rightStep, ha, hb] using
            And.intro hxq (show d ≤ c + 1 by omega)
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
          have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyp : y ∈ (σ.extPositions j).filter (p < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1,
              by simp only [decide_eq_true_eq]; omega⟩
          have hhead : ((σ.extPositions j).filter (p < ·)).head
              (List.ne_nil_of_mem hyp) = x := by
            rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
            exact Option.some.inj ha
          have hxy : x ≤ y := by
            simpa only [hhead] using ((hSort j).filter _).rel_head hyp
          simpa only [rightStep, ha, hb] using
            And.intro hxy (show d + 1 ≤ c + 1 by omega)
    have hFoldLeft : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
        (ls.foldl (leftStep σ) (p, c)).1 ≤ (ls.foldl (leftStep σ) (q, d)).1 ∧
        (ls.foldl (leftStep σ) (p, c)).2 ≤ (ls.foldl (leftStep σ) (q, d)).2 := by
      intro ls
      induction ls with
      | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
      | cons j ls ih =>
        intro p q c d hpq hcd
        have h := hStepLeft j p q c d hpq hcd
        simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
    have hFoldRight : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
        (ls.foldl (rightStep σ) (p, c)).1 ≤ (ls.foldl (rightStep σ) (q, d)).1 ∧
        (ls.foldl (rightStep σ) (q, d)).2 ≤ (ls.foldl (rightStep σ) (p, c)).2 := by
      intro ls
      induction ls with
      | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
      | cons j ls ih =>
        intro p q c d hpq hcd
        have h := hStepRight j p q c d hpq hcd
        simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
    constructor
    · simp only [leftExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩,
        (hFoldLeft ls p q 0 0 hpq le_rfl).2⟩
    · simp only [rightExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩,
        (hFoldRight ls p q 0 0 hpq le_rfl).2⟩

end ErdosSzekeres
