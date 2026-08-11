module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 17. -/

theorem halfPureDeepSplitFin8_clause2722 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom253 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom044 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom050 at h4
  unfold HalfPureDeepSplitFin8Atom053 at h5
  unfold HalfPureDeepSplitFin8Atom253 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {2, 3, 4, 6}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask092
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 4, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2738 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom254 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom254 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {2, 3, 4, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask156
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2744 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom241 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom024 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom241 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {1, 2, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask198
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 2, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2749 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom257 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom257 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {2, 3, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask204
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2754 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom250 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom031 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom250 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {1, 4, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask210
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2756 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom260 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom260 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {2, 4, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask212
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2760 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom264 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom050 at h1
  unfold HalfPureDeepSplitFin8Atom051 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom264 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{5}, {3, 4, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask216
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {3, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2941 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom163 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom023 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom031 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom041 at h4
  unfold HalfPureDeepSplitFin8Atom047 at h5
  unfold HalfPureDeepSplitFin8Atom163 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 3, 5}, {4}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask046
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 3, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 3 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2947 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom163 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom026 at h0
  unfold HalfPureDeepSplitFin8Atom030 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom040 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom051 at h5
  unfold HalfPureDeepSplitFin8Atom163 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 3, 5}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask046
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 3, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 3 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3036 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom166 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom028 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom038 at h4
  unfold HalfPureDeepSplitFin8Atom047 at h5
  unfold HalfPureDeepSplitFin8Atom166 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 4, 5}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask054
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3042 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom166 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom026 at h0
  unfold HalfPureDeepSplitFin8Atom033 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom043 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom166 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 4, 5}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask054
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3087 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom172 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom030 at h0
  unfold HalfPureDeepSplitFin8Atom033 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom172 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 4, 5}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask058
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 3, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3104 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom182 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom023 at h1
  unfold HalfPureDeepSplitFin8Atom024 at h2
  unfold HalfPureDeepSplitFin8Atom027 at h3
  unfold HalfPureDeepSplitFin8Atom028 at h4
  unfold HalfPureDeepSplitFin8Atom031 at h5
  unfold HalfPureDeepSplitFin8Atom182 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 4, 5}, {1}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask060
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 3, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3110 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom182 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom043 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom182 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 4, 5}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask060
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 3, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3154 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom252 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom039 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom044 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom050 at h4
  unfold HalfPureDeepSplitFin8Atom053 at h5
  unfold HalfPureDeepSplitFin8Atom252 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {2, 3, 4, 5}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask060
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3168 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom244 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom029 at h0
  unfold HalfPureDeepSplitFin8Atom032 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom244 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {1, 3, 4, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask154
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3170 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom254 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom039 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom254 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {2, 3, 4, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask156
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3179 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom246 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom029 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom246 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {1, 3, 5, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask170
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 3, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3181 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom256 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom039 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom256 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {2, 3, 5, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask172
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3188 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom259 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom042 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom259 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {2, 4, 5, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask180
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3192 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom263 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom048 at h0
  unfold HalfPureDeepSplitFin8Atom050 at h1
  unfold HalfPureDeepSplitFin8Atom052 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom263 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{6}, {3, 4, 5, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask184
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {3, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3375 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom164 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom024 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom034 at h2
  unfold HalfPureDeepSplitFin8Atom038 at h3
  unfold HalfPureDeepSplitFin8Atom044 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom164 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 3, 6}, {5}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask078
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 3, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 3 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3468 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom167 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom039 at h4
  unfold HalfPureDeepSplitFin8Atom048 at h5
  unfold HalfPureDeepSplitFin8Atom167 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 4, 6}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask086
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 4, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3519 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom173 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom030 at h0
  unfold HalfPureDeepSplitFin8Atom033 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom173 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 4, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask090
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 3, 4, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

end ErdosSzekeres

end
