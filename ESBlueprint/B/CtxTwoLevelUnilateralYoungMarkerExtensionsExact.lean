import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- For two indexed same-side levels with maxima [1,m], a nonempty youngest marker list entirely right of p gives an exact unilateral extension profile. The right chain gains a second slot exactly when a youngest marker precedes an older marker; the older join term is m+1 and the opposite indexed extensions vanish. This ordered-thread profile supports an outer-run witness for ROOT-NF on axis two.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_two_level_unilateral_young_marker_extensions_exact (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [1, m])
    (s : Ctx.Side) (hs1 : σ.sideAt 1 = s) (hs2 : σ.sideAt 2 = s)
    (p : ℕ) (hn : σ.extPositions 1 ≠ [])
    (hfresh : ∀ x ∈ σ.extPositions 1, p < x) :
    let left := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
    let right := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
    σ.leftExt s 0 p = left ∧ σ.rightExt s 0 p = right ∧
      σ.joinExt s p p = max (left + right) (m + 1) ∧
      (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0) := by
  classical
  let L := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
  let R := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
  change σ.leftExt s 0 p = L ∧ σ.rightExt s 0 p = R ∧
    σ.joinExt s p p = max (L + R) (m + 1) ∧
    (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0)
  have hlevels : σ.levelsOn s 0 = [1, 2] := by
    simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
  have hbelow : σ.levelsOn s 2 = [1] := by
    simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
  obtain ⟨a, tail, hA⟩ := List.exists_cons_of_ne_nil hn
  have ha : a ∈ σ.extPositions 1 := by rw [hA]; simp
  have hpa : p < a := hfresh a ha
  have hsorted : (σ.extPositions 1).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hmin : ∀ x ∈ σ.extPositions 1, a ≤ x := by
    intro x hx
    simpa [hA] using hsorted.rel_head hx
  have hleftA : (σ.extPositions 1).filter (· < p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hp := hfresh x hx
    simp only [decide_eq_true_eq]
    omega
  have hrightA : (σ.extPositions 1).filter (p < ·) = σ.extPositions 1 := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using hfresh x hx
  have hheadA : ((σ.extPositions 1).filter (p < ·)).head? = some a := by
    rw [hrightA, hA]
    rfl
  have hthread : (∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) ↔
      (σ.extPositions 2).filter (a < ·) ≠ [] := by
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      have hxy' : a < y := lt_of_le_of_lt (hmin x hx) hxy
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hy, by simpa using hxy'⟩)
    · intro hne
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨a, ha, y, (List.mem_filter.mp hy).1,
        of_decide_eq_true (List.mem_filter.mp hy).2⟩
  have hleft : σ.leftExt s 0 p = L := by
    cases hB : ((σ.extPositions 2).filter (· < p)).getLast? with
    | none =>
      have he : (σ.extPositions 2).filter (· < p) = [] := List.getLast?_eq_none_iff.mp hB
      simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
        List.sublists_cons, hleftA, hB, L, he,
        -List.getLast?_filter, -List.getLast_filter]
    | some b =>
      have hne : (σ.extPositions 2).filter (· < p) ≠ [] := by
        intro he
        simp [he] at hB
      simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
        List.sublists_cons, hleftA, hB, L, hne,
        -List.getLast?_filter, -List.getLast_filter]
  have hright : σ.rightExt s 0 p = R := by
    cases hB : ((σ.extPositions 2).filter (p < ·)).head? with
    | none =>
      cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
      | none =>
        have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
        have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
          intro ht
          exact (hthread.mp ht) he
        simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
          List.sublists_cons, hheadA, hB, hC, R, ht,
          -List.head?_filter, -List.head_filter]
      | some c =>
        have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
          intro he
          simp [he] at hC
        have ht := hthread.mpr hne
        simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
          List.sublists_cons, hheadA, hB, hC, R, ht,
          -List.head?_filter, -List.head_filter]
    | some b =>
      cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
      | none =>
        have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
        have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
          intro ht
          exact (hthread.mp ht) he
        simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
          List.sublists_cons, hheadA, hB, hC, R, ht,
          -List.head?_filter, -List.head_filter]
      | some c =>
        have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
          intro he
          simp [he] at hC
        have ht := hthread.mpr hne
        simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
          List.sublists_cons, hheadA, hB, hC, R, ht,
          -List.head?_filter, -List.head_filter]
  have hleftBelow : σ.leftExt s 2 p = 0 := by
    simp [Ctx.Context.leftExt_eq, hbelow, Ctx.Context.leftStep, hleftA,
      -List.getLast?_filter]
  have hrightBelow : σ.rightExt s 2 p = 1 := by
    simp [Ctx.Context.rightExt_eq, hbelow, Ctx.Context.rightStep, hheadA,
      -List.head?_filter]
  have hchain : σ.chainExt s p p = L + R := by
    simp only [Ctx.Context.chainExt, hleft, hright]
  have hjoin : σ.joinExt s p p = max (L + R) (m + 1) := by
    simp [Ctx.Context.joinExt, hlevels, hchain, Ctx.Context.leftExt_one,
      Ctx.Context.rightExt_one, hleftBelow, hrightBelow,
      Ctx.Context.maximumAt, hmax, Nat.add_comm]
  refine ⟨hleft, hright, hjoin, ?_⟩
  intro t ht
  have hs : s ≠ t := Ne.symm ht
  have hother : σ.levelsOn t 0 = [] := by
    simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, hs, List.range_succ]
  have hc : σ.chainExt t p p = 0 := by
    simp [Ctx.Context.chainExt, Ctx.Context.leftExt_eq, Ctx.Context.rightExt_eq, hother]
  exact ⟨hc, by simp [Ctx.Context.joinExt, hother, hc]⟩

end ErdosSzekeres
