module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 9. -/

theorem halfPureDeepSplitFin8_clause1058 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom119 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom043 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1059 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom119 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1060 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom119 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1062 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom119 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1064 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom119 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom119 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1065 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom120 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1066 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom120 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1067 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom120 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1068 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom120 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1070 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom120 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1071 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom120 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1072 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom120 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom120 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1074 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom121 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom121 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1075 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom121 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom121 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1076 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom121 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom121 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1078 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom121 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom121 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1080 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom121 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom121 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1081 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom122 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom122 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1082 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom122 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom122 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1083 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom122 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom122 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1084 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom122 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom122 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1086 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom122 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom050
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom122 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1089 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1090 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
