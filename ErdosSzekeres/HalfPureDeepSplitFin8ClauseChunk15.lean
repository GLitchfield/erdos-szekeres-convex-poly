module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 15. -/

theorem halfPureDeepSplitFin8_clause1952 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1953 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1954 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1955 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom266 χ ∧
      ¬HalfPureDeepSplitFin8Atom126 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom266 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1956 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom266 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom266 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1957 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom266 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom266 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1958 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom266 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom266 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1960 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom056 χ ∧
      ¬HalfPureDeepSplitFin8Atom266 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom266 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1996 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom092 χ ∧
      HalfPureDeepSplitFin8Atom093 χ ∧
      HalfPureDeepSplitFin8Atom096 χ ∧
      HalfPureDeepSplitFin8Atom102 χ ∧
      HalfPureDeepSplitFin8Atom112 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {1, 2, 3, 4, 5} := by
    intro hstrong
    exact hnoStrong ⟨{1, 2, 3, 4, 5}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom092 HalfPureDeepSplitFin8Atom093 HalfPureDeepSplitFin8Atom096
    HalfPureDeepSplitFin8Atom102 HalfPureDeepSplitFin8Atom112 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2002 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom096 χ ∧
      HalfPureDeepSplitFin8Atom097 χ ∧
      HalfPureDeepSplitFin8Atom099 χ ∧
      HalfPureDeepSplitFin8Atom108 χ ∧
      HalfPureDeepSplitFin8Atom118 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {1, 2, 4, 5, 6} := by
    intro hstrong
    exact hnoStrong ⟨{1, 2, 4, 5, 6}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    1 2 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom096 HalfPureDeepSplitFin8Atom097 HalfPureDeepSplitFin8Atom099
    HalfPureDeepSplitFin8Atom108 HalfPureDeepSplitFin8Atom118 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2004 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom097 χ ∧
      HalfPureDeepSplitFin8Atom098 χ ∧
      HalfPureDeepSplitFin8Atom101 χ ∧
      HalfPureDeepSplitFin8Atom110 χ ∧
      HalfPureDeepSplitFin8Atom120 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {1, 2, 4, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{1, 2, 4, 6, 7}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    1 2 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom097 HalfPureDeepSplitFin8Atom098 HalfPureDeepSplitFin8Atom101
    HalfPureDeepSplitFin8Atom110 HalfPureDeepSplitFin8Atom120 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2006 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom102 χ ∧
      HalfPureDeepSplitFin8Atom103 χ ∧
      HalfPureDeepSplitFin8Atom105 χ ∧
      HalfPureDeepSplitFin8Atom108 χ ∧
      HalfPureDeepSplitFin8Atom122 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {1, 3, 4, 5, 6} := by
    intro hstrong
    exact hnoStrong ⟨{1, 3, 4, 5, 6}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    1 3 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom102 HalfPureDeepSplitFin8Atom103 HalfPureDeepSplitFin8Atom105
    HalfPureDeepSplitFin8Atom108 HalfPureDeepSplitFin8Atom122 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2011 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom112 χ ∧
      HalfPureDeepSplitFin8Atom113 χ ∧
      HalfPureDeepSplitFin8Atom115 χ ∧
      HalfPureDeepSplitFin8Atom118 χ ∧
      HalfPureDeepSplitFin8Atom122 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 5, 6} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    2 3 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom112 HalfPureDeepSplitFin8Atom113 HalfPureDeepSplitFin8Atom115
    HalfPureDeepSplitFin8Atom118 HalfPureDeepSplitFin8Atom122 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2015 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom118 χ ∧
      HalfPureDeepSplitFin8Atom119 χ ∧
      HalfPureDeepSplitFin8Atom120 χ ∧
      HalfPureDeepSplitFin8Atom121 χ ∧
      HalfPureDeepSplitFin8Atom126 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 4, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    2 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom118 HalfPureDeepSplitFin8Atom119 HalfPureDeepSplitFin8Atom120
    HalfPureDeepSplitFin8Atom121 HalfPureDeepSplitFin8Atom126 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2016 (χ : TripleColoring 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :
    ¬(HalfPureDeepSplitFin8Atom122 χ ∧
      HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom126 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {3, 4, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7}, by simp, by decide, hstrong⟩
  have hor := strongPredecessorFin8_notStrongFive_quads χ
    3 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot
  unfold HalfPureDeepSplitFin8Atom122 HalfPureDeepSplitFin8Atom123 HalfPureDeepSplitFin8Atom124
    HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom126 at hbad
  tauto

theorem halfPureDeepSplitFin8_clause2094 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom255 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom024 at h1
  unfold HalfPureDeepSplitFin8Atom025 at h2
  unfold HalfPureDeepSplitFin8Atom028 at h3
  unfold HalfPureDeepSplitFin8Atom029 at h4
  unfold HalfPureDeepSplitFin8Atom034 at h5
  unfold HalfPureDeepSplitFin8Atom255 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {2, 3, 5, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2099 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom262 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom029 at h2
  unfold HalfPureDeepSplitFin8Atom031 at h3
  unfold HalfPureDeepSplitFin8Atom032 at h4
  unfold HalfPureDeepSplitFin8Atom034 at h5
  unfold HalfPureDeepSplitFin8Atom262 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {3, 4, 5, 6}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2110 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom256 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom024 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom028 at h3
  unfold HalfPureDeepSplitFin8Atom030 at h4
  unfold HalfPureDeepSplitFin8Atom035 at h5
  unfold HalfPureDeepSplitFin8Atom256 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {2, 3, 5, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2115 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom263 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom028 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom031 at h3
  unfold HalfPureDeepSplitFin8Atom033 at h4
  unfold HalfPureDeepSplitFin8Atom035 at h5
  unfold HalfPureDeepSplitFin8Atom263 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {3, 4, 5, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2121 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom257 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom022 at h0
  unfold HalfPureDeepSplitFin8Atom025 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom029 at h3
  unfold HalfPureDeepSplitFin8Atom030 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom257 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {2, 3, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2124 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom023 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom260 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom023 at h0
  unfold HalfPureDeepSplitFin8Atom025 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom032 at h3
  unfold HalfPureDeepSplitFin8Atom033 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom260 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {2, 4, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2126 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom264 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom027 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom032 at h3
  unfold HalfPureDeepSplitFin8Atom033 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom264 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {3, 4, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2131 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom261 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom024 at h0
  unfold HalfPureDeepSplitFin8Atom025 at h1
  unfold HalfPureDeepSplitFin8Atom026 at h2
  unfold HalfPureDeepSplitFin8Atom034 at h3
  unfold HalfPureDeepSplitFin8Atom035 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom261 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {2, 5, 6, 7}, ?_, Or.inr ?_⟩
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

theorem halfPureDeepSplitFin8_clause2133 (χ : TripleColoring 8)
    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  unfold HalfPureDeepSplitFin8Atom028 at h0
  unfold HalfPureDeepSplitFin8Atom029 at h1
  unfold HalfPureDeepSplitFin8Atom030 at h2
  unfold HalfPureDeepSplitFin8Atom034 at h3
  unfold HalfPureDeepSplitFin8Atom035 at h4
  unfold HalfPureDeepSplitFin8Atom036 at h5
  unfold HalfPureDeepSplitFin8Atom265 at h6
  apply hno
  unfold HalfPureDeepSplitFin8Conclusion
  refine ⟨{1}, {3, 5, 6, 7}, ?_, Or.inr ?_⟩
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

end ErdosSzekeres

end
