module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 10. -/

theorem halfPureDeepSplitFin8_clause1091 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1092 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1094 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom123 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom051
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1095 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom051
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom123 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1097 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1098 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1099 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1100 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1102 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom124 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1103 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1104 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1105 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1106 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1107 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1108 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1109 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom125 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1110 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom125 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1111 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1112 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom125 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1113 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom126 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1114 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom126 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1115 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom126 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1116 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom126 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom126 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1118 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom126 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom126 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
