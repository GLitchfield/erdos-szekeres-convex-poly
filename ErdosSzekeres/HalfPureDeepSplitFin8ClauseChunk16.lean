module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 16. -/

theorem halfPureDeepSplitFin8_clause2183 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom248 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom023 at h0
  unfold HalfPureDeepSplitFin8Atom024 at h1
  unfold HalfPureDeepSplitFin8Atom025 at h2
  unfold HalfPureDeepSplitFin8Atom041 at h3
  unfold HalfPureDeepSplitFin8Atom042 at h4
  unfold HalfPureDeepSplitFin8Atom044 at h5
  unfold HalfPureDeepSplitFin8Atom248 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {1, 4, 5, 6}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2185 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom262 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom039 at h2
  unfold HalfPureDeepSplitFin8Atom041 at h3
  unfold HalfPureDeepSplitFin8Atom042 at h4
  unfold HalfPureDeepSplitFin8Atom044 at h5
  unfold HalfPureDeepSplitFin8Atom262 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {3, 4, 5, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2201 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom263 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom041 at h3
  unfold HalfPureDeepSplitFin8Atom043 at h4
  unfold HalfPureDeepSplitFin8Atom045 at h5
  unfold HalfPureDeepSplitFin8Atom263 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {3, 4, 5, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2212 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom264 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom042 at h3
  unfold HalfPureDeepSplitFin8Atom043 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom264 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {3, 4, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2219 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom265 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {3, 5, 6, 7}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {3, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2223 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom266 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom266 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2}, {4, 5, 6, 7}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {4, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      4 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2285 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom236 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom028 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom038 at h4
  unfold HalfPureDeepSplitFin8Atom047 at h5
  unfold HalfPureDeepSplitFin8Atom236 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 2, 4, 5}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 2, 4, 5}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 5 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2290 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom237 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom039 at h4
  unfold HalfPureDeepSplitFin8Atom048 at h5
  unfold HalfPureDeepSplitFin8Atom237 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 2, 4, 6}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 2, 4, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2294 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom239 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom038 at h3
  unfold HalfPureDeepSplitFin8Atom039 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom239 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 2, 5, 6}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 2, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2297 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom248 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom248 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 4, 5, 6}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 4, 5, 6}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 6 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2299 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom258 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom039 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom050 at h5
  unfold HalfPureDeepSplitFin8Atom258 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {2, 4, 5, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2306 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom238 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom027 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom037 at h3
  unfold HalfPureDeepSplitFin8Atom040 at h4
  unfold HalfPureDeepSplitFin8Atom049 at h5
  unfold HalfPureDeepSplitFin8Atom238 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 2, 4, 7}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {1, 2, 4, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 4 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2313 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom249 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom051 at h5
  unfold HalfPureDeepSplitFin8Atom249 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 4, 5, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask178
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2315 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom259 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom051 at h5
  unfold HalfPureDeepSplitFin8Atom259 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {2, 4, 5, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2321 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom241 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom039 at h3
  unfold HalfPureDeepSplitFin8Atom040 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom241 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 2, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2324 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom250 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom250 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 4, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2331 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom251 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom028 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom251 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {1, 5, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask226
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {1, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2337 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom266 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom048 at h1
  unfold HalfPureDeepSplitFin8Atom049 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom266 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3}, {4, 5, 6, 7}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {4, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      4 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2463 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom255 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom042 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom048 at h4
  unfold HalfPureDeepSplitFin8Atom053 at h5
  unfold HalfPureDeepSplitFin8Atom255 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4}, {2, 3, 5, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2479 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom256 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom256 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4}, {2, 3, 5, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2490 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom257 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom257 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4}, {2, 3, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2497 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom261 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom261 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4}, {2, 5, 6, 7}, ?_, Or.inr ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask228
      polygon hsub (by omega)
    subst polygon
    show IsCapSet χ {2, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2501 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom048 at h1
  unfold HalfPureDeepSplitFin8Atom049 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom265 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{4}, {3, 5, 6, 7}, ?_, Or.inr ?_⟩
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
    show IsCapSet χ {3, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause2688 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom162 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom026 at h0
  unfold HalfPureDeepSplitFin8Atom030 at h1
  unfold HalfPureDeepSplitFin8Atom033 at h2
  unfold HalfPureDeepSplitFin8Atom040 at h3
  unfold HalfPureDeepSplitFin8Atom043 at h4
  unfold HalfPureDeepSplitFin8Atom049 at h5
  unfold HalfPureDeepSplitFin8Atom162 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 3, 4}, {7}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask030
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 2, 3, 4}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 3 4 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

end ErdosSzekeres

end
