module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 13. -/

theorem halfPureDeepSplitFin8_clause1537 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom196 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom196 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1538 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom196 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom196 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1775 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom236 χ ∧
      ¬HalfPureDeepSplitFin8Atom096 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom096 HalfPureDeepSplitFin8Atom236 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1781 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom237 χ ∧
      ¬HalfPureDeepSplitFin8Atom097 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom097 HalfPureDeepSplitFin8Atom237 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1787 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom238 χ ∧
      ¬HalfPureDeepSplitFin8Atom098 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom098 HalfPureDeepSplitFin8Atom238 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1793 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom239 χ ∧
      ¬HalfPureDeepSplitFin8Atom099 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom099 HalfPureDeepSplitFin8Atom239 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1805 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom241 χ ∧
      ¬HalfPureDeepSplitFin8Atom101 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom101 HalfPureDeepSplitFin8Atom241 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1811 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom242 χ ∧
      ¬HalfPureDeepSplitFin8Atom102 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom102 HalfPureDeepSplitFin8Atom242 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1823 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom244 χ ∧
      ¬HalfPureDeepSplitFin8Atom104 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom104 HalfPureDeepSplitFin8Atom244 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1829 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom245 χ ∧
      ¬HalfPureDeepSplitFin8Atom105 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom105 HalfPureDeepSplitFin8Atom245 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1835 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom246 χ ∧
      ¬HalfPureDeepSplitFin8Atom106 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom106 HalfPureDeepSplitFin8Atom246 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1847 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom248 χ ∧
      ¬HalfPureDeepSplitFin8Atom108 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom108 HalfPureDeepSplitFin8Atom248 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1848 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom248 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom032 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom248 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1853 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom249 χ ∧
      ¬HalfPureDeepSplitFin8Atom109 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom109 HalfPureDeepSplitFin8Atom249 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1854 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom249 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom249 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1859 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom250 χ ∧
      ¬HalfPureDeepSplitFin8Atom110 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom110 HalfPureDeepSplitFin8Atom250 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1865 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom251 χ ∧
      ¬HalfPureDeepSplitFin8Atom111 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom111 HalfPureDeepSplitFin8Atom251 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1866 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom251 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom251 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1871 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom252 χ ∧
      ¬HalfPureDeepSplitFin8Atom112 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom112 HalfPureDeepSplitFin8Atom252 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1877 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom253 χ ∧
      ¬HalfPureDeepSplitFin8Atom113 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom113 HalfPureDeepSplitFin8Atom253 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1878 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom253 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom253 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1883 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom254 χ ∧
      ¬HalfPureDeepSplitFin8Atom114 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom114 HalfPureDeepSplitFin8Atom254 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1889 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom255 χ ∧
      ¬HalfPureDeepSplitFin8Atom115 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom115 HalfPureDeepSplitFin8Atom255 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1890 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom255 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom255 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
