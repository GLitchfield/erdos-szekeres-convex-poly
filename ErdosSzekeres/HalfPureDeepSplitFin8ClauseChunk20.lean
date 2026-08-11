module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 20. -/

theorem halfPureDeepSplitFin8_clause4979 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom195 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom048 at h1
  unfold HalfPureDeepSplitFin8Atom049 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom195 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 5, 6, 7}, {4}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask232
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {3, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause5022 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom196 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom196 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4, 5, 6, 7}, {2}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask240
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {4, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      4 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause5026 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom196 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom048 at h1
  unfold HalfPureDeepSplitFin8Atom049 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom196 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4, 5, 6, 7}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask240
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {4, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      4 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

end ErdosSzekeres

end
