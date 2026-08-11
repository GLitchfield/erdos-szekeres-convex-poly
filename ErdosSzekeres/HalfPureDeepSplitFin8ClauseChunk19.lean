module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 19. -/

theorem halfPureDeepSplitFin8_clause4422 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom176 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom029 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom036 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom176 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 5, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 3, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4441 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom186 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom041 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom054 at h5
  unfold HalfPureDeepSplitFin8Atom186 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 5, 7}, {4}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4445 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom186 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom039 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom052 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom186 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 3, 5, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 3 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4496 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom179 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom051 at h5
  unfold HalfPureDeepSplitFin8Atom179 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 4, 5, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4519 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom189 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom047 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom051 at h5
  unfold HalfPureDeepSplitFin8Atom189 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 5, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4523 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom189 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom042 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom046 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom189 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 5, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4550 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom193 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom031 at h3
  unfold HalfPureDeepSplitFin8Atom033 at h4
  unfold HalfPureDeepSplitFin8Atom035 at h5
  unfold HalfPureDeepSplitFin8Atom193 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 7}, {1}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {3, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4552 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom193 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom038 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom041 at h3
  unfold HalfPureDeepSplitFin8Atom043 at h4
  unfold HalfPureDeepSplitFin8Atom045 at h5
  unfold HalfPureDeepSplitFin8Atom193 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 7}, {2}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {3, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4556 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom193 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom048 at h0
  unfold HalfPureDeepSplitFin8Atom050 at h1
  unfold HalfPureDeepSplitFin8Atom052 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom055 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom193 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 5, 7}, {6}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {3, 4, 5, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 5 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4669 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom171 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom039 at h3
  unfold HalfPureDeepSplitFin8Atom040 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom171 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 6, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 2, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4675 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom171 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom024 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom171 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 2, 6, 7}, {5}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 2, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 2 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4716 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom177 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom032 at h1
  unfold HalfPureDeepSplitFin8Atom033 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom177 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 6, 7}, {4}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask202
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 3, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4720 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom177 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom028 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom177 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 3, 6, 7}, {5}, ?_, Or.inl ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · refine ⟨by simp, by decide, ?_⟩
    intro polygon hsub hcard hstrong
    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask202
      polygon hsub (by omega)
    subst polygon
    show IsCupSet χ {1, 3, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 3 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4794 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom180 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom180 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 4, 6, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4798 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom180 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom031 at h0
  unfold HalfPureDeepSplitFin8Atom034 at h1
  unfold HalfPureDeepSplitFin8Atom035 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom180 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 4, 6, 7}, {5}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4817 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom190 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom048 at h3
  unfold HalfPureDeepSplitFin8Atom049 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom190 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 6, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4821 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom190 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom044 at h1
  unfold HalfPureDeepSplitFin8Atom045 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom190 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 4, 6, 7}, {5}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4850 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom194 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom037 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom042 at h3
  unfold HalfPureDeepSplitFin8Atom043 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom194 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 6, 7}, {2}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {3, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4854 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom194 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom047 at h0
  unfold HalfPureDeepSplitFin8Atom050 at h1
  unfold HalfPureDeepSplitFin8Atom051 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom056 at h5
  unfold HalfPureDeepSplitFin8Atom194 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 4, 6, 7}, {5}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {3, 4, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      3 4 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4917 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom181 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom024 at h0
  unfold HalfPureDeepSplitFin8Atom025 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom181 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1, 5, 6, 7}, {2}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {1, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      1 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4942 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom191 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom050 at h3
  unfold HalfPureDeepSplitFin8Atom051 at h4
  unfold HalfPureDeepSplitFin8Atom052 at h5
  unfold HalfPureDeepSplitFin8Atom191 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 5, 6, 7}, {3}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4946 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom191 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom041 at h0
  unfold HalfPureDeepSplitFin8Atom042 at h1
  unfold HalfPureDeepSplitFin8Atom043 at h2
  unfold HalfPureDeepSplitFin8Atom053 at h3
  unfold HalfPureDeepSplitFin8Atom054 at h4
  unfold HalfPureDeepSplitFin8Atom055 at h5
  unfold HalfPureDeepSplitFin8Atom191 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{2, 5, 6, 7}, {4}, ?_, Or.inl ?_⟩
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
    show IsCupSet χ {2, 5, 6, 7}
    by_contra hnotPure
    apply h6
    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ
      2 5 6 7 (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩

theorem halfPureDeepSplitFin8_clause4973 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom195 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom028 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom034 at h3
  unfold HalfPureDeepSplitFin8Atom035 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom195 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 5, 6, 7}, {1}, ?_, Or.inl ?_⟩
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

theorem halfPureDeepSplitFin8_clause4975 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom195 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom038 at h0
  unfold HalfPureDeepSplitFin8Atom039 at h1
  unfold HalfPureDeepSplitFin8Atom040 at h2
  unfold HalfPureDeepSplitFin8Atom044 at h3
  unfold HalfPureDeepSplitFin8Atom045 at h4
  unfold HalfPureDeepSplitFin8Atom046 at h5
  unfold HalfPureDeepSplitFin8Atom195 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{3, 5, 6, 7}, {2}, ?_, Or.inl ?_⟩
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

end ErdosSzekeres

end
