module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 12. -/

theorem halfPureDeepSplitFin8_clause1463 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom184 χ ∧
      ¬HalfPureDeepSplitFin8Atom114 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom114 HalfPureDeepSplitFin8Atom184 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1464 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom184 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom184 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1469 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom185 χ ∧
      ¬HalfPureDeepSplitFin8Atom115 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom115 HalfPureDeepSplitFin8Atom185 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1470 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom185 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom185 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1475 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom186 χ ∧
      ¬HalfPureDeepSplitFin8Atom116 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom116 HalfPureDeepSplitFin8Atom186 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1487 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom188 χ ∧
      ¬HalfPureDeepSplitFin8Atom118 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom118 HalfPureDeepSplitFin8Atom188 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1488 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom188 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom188 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1493 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom189 χ ∧
      ¬HalfPureDeepSplitFin8Atom119 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom119 HalfPureDeepSplitFin8Atom189 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1494 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom189 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom189 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1499 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom190 χ ∧
      ¬HalfPureDeepSplitFin8Atom120 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom120 HalfPureDeepSplitFin8Atom190 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1500 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom190 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom190 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1505 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom191 χ ∧
      ¬HalfPureDeepSplitFin8Atom121 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom121 HalfPureDeepSplitFin8Atom191 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1506 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom191 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom046 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom044 HalfPureDeepSplitFin8Atom045 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom191 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1511 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom192 χ ∧
      ¬HalfPureDeepSplitFin8Atom122 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom122 HalfPureDeepSplitFin8Atom192 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1512 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom192 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom050
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom192 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1517 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom193 χ ∧
      ¬HalfPureDeepSplitFin8Atom123 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom123 HalfPureDeepSplitFin8Atom193 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1518 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom193 χ ∧
      HalfPureDeepSplitFin8Atom047 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom051
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom193 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1523 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom194 χ ∧
      ¬HalfPureDeepSplitFin8Atom124 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom124 HalfPureDeepSplitFin8Atom194 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1524 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom194 χ ∧
      HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom194 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1526 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom194 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom124 HalfPureDeepSplitFin8Atom194 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1529 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom195 χ ∧
      ¬HalfPureDeepSplitFin8Atom125 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom195 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1530 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom195 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom195 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1535 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom196 χ ∧
      ¬HalfPureDeepSplitFin8Atom126 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom126 HalfPureDeepSplitFin8Atom196 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1536 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom196 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom196 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
