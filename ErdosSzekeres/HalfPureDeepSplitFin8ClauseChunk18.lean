module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 18. -/

theorem halfPureDeepSplitFin8_clause3542 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom183 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom043 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom183 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 4, 6}, {7}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 4, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3641 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom169 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom038 at h3
  unfold HalfPureDeepSplitFin8Atom039 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom169 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 5, 6}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask102
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3692 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom175 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom030 at h0
  unfold HalfPureDeepSplitFin8Atom035 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom051 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom175 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 5, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask106
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 3, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3711 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom185 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom042 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom053 at h5
  unfold HalfPureDeepSplitFin8Atom185 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 5, 6}, {4}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask108
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 3, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3715 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom185 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom045 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom051 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom185 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 5, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask108
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 3, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3766 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom178 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom178 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 4, 5, 6}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask114
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3770 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom178 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom033 at h0
  unfold HalfPureDeepSplitFin8Atom035 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom054 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom178 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 4, 5, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask114
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3789 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom188 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom039 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom188 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 5, 6}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask116
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3793 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom188 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom043 at h0
  unfold HalfPureDeepSplitFin8Atom045 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom054 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom188 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 5, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask116
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {2, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3820 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom192 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom031 at h3
  unfold HalfPureDeepSplitFin8Atom032 at h4
  unfold HalfPureDeepSplitFin8Atom034 at h5
  unfold HalfPureDeepSplitFin8Atom192 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 6}, {1}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask120
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {3, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3822 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom192 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom039 at h2
  unfold HalfPureDeepSplitFin8Atom041 at h3
  unfold HalfPureDeepSplitFin8Atom042 at h4
  unfold HalfPureDeepSplitFin8Atom044 at h5
  unfold HalfPureDeepSplitFin8Atom192 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 6}, {2}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask120
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {3, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3826 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom192 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom049 at h0
  unfold HalfPureDeepSplitFin8Atom051 at h1
  unfold HalfPureDeepSplitFin8Atom052 at h2
  unfold HalfPureDeepSplitFin8Atom054 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom192 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 6}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask120
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {3, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3882 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom242 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom030 at h0
  unfold HalfPureDeepSplitFin8Atom033 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom242 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {1, 3, 4, 5}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 3, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3884 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom252 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom043 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom252 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {2, 3, 4, 5}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause3900 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom253 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom043 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom049 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom253 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {2, 3, 4, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause3909 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom245 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom030 at h0
  unfold HalfPureDeepSplitFin8Atom035 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom051 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom245 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {1, 3, 5, 6}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask106
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 3, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3911 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom255 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom040 at h0
  unfold HalfPureDeepSplitFin8Atom045 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom051 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom255 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {2, 3, 5, 6}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask108
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 3, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3918 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom258 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom043 at h0
  unfold HalfPureDeepSplitFin8Atom045 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom054 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom258 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {2, 4, 5, 6}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask116
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause3922 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom262 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom049 at h0
  unfold HalfPureDeepSplitFin8Atom051 at h1
  unfold HalfPureDeepSplitFin8Atom052 at h2
  unfold HalfPureDeepSplitFin8Atom054 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom262 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{7}, {3, 4, 5, 6}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask120
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {3, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4198 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom168 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom040 at h4
  unfold HalfPureDeepSplitFin8Atom049 at h5
  unfold HalfPureDeepSplitFin8Atom168 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 4, 7}, {3}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask150
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4245 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom174 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom028 at h0
  unfold HalfPureDeepSplitFin8Atom031 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom174 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 4, 7}, {5}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4249 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom174 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom029 at h0
  unfold HalfPureDeepSplitFin8Atom032 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom174 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 4, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4266 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom184 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom023 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom027 at h3
  unfold HalfPureDeepSplitFin8Atom030 at h4
  unfold HalfPureDeepSplitFin8Atom033 at h5
  unfold HalfPureDeepSplitFin8Atom184 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 4, 7}, {1}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4272 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom184 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom039 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom184 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 4, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

end ErdosSzekeres

end
