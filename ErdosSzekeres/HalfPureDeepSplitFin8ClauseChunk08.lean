module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 8. -/

theorem halfPureDeepSplitFin8_clause1003 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom112 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom112 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1004 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom112 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom112 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1009 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom113 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom113 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1010 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom113 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom113 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1012 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom113 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom113 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1018 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom114 χ ∧
      ¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom114 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1019 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom114 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom114 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1020 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom114 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom114 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1025 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom115 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom115 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1026 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom115 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom115 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1027 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom115 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom115 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1028 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom115 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom115 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1033 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom116 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom116 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1034 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom116 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom116 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1035 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom116 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom116 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1036 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom116 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom116 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1043 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom117 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom117 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1044 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom117 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom117 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1049 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom118 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom118 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1050 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom118 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom118 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1051 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom118 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom118 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1052 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom118 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom118 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1054 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom118 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom118 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1057 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom119 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
