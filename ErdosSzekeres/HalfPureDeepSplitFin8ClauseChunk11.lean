module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 11. -/

theorem halfPureDeepSplitFin8_clause1119 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
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

theorem halfPureDeepSplitFin8_clause1120 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom126 χ ∧
      HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
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

theorem halfPureDeepSplitFin8_clause1331 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom162 χ ∧
      ¬HalfPureDeepSplitFin8Atom092 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom092 HalfPureDeepSplitFin8Atom162 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1337 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom163 χ ∧
      ¬HalfPureDeepSplitFin8Atom093 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom093 HalfPureDeepSplitFin8Atom163 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1338 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom163 χ ∧
      HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom038 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom028
    HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom163 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1343 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom164 χ ∧
      ¬HalfPureDeepSplitFin8Atom094 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom094 HalfPureDeepSplitFin8Atom164 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1355 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom166 χ ∧
      ¬HalfPureDeepSplitFin8Atom096 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom096 HalfPureDeepSplitFin8Atom166 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1361 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom167 χ ∧
      ¬HalfPureDeepSplitFin8Atom097 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom097 HalfPureDeepSplitFin8Atom167 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1367 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom168 χ ∧
      ¬HalfPureDeepSplitFin8Atom098 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom098 HalfPureDeepSplitFin8Atom168 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1373 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom169 χ ∧
      ¬HalfPureDeepSplitFin8Atom099 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom099 HalfPureDeepSplitFin8Atom169 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1385 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom171 χ ∧
      ¬HalfPureDeepSplitFin8Atom101 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom101 HalfPureDeepSplitFin8Atom171 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1391 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom172 χ ∧
      ¬HalfPureDeepSplitFin8Atom102 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom102 HalfPureDeepSplitFin8Atom172 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1397 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom173 χ ∧
      ¬HalfPureDeepSplitFin8Atom103 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom103 HalfPureDeepSplitFin8Atom173 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1403 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom174 χ ∧
      ¬HalfPureDeepSplitFin8Atom104 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom104 HalfPureDeepSplitFin8Atom174 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1409 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom175 χ ∧
      ¬HalfPureDeepSplitFin8Atom105 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom105 HalfPureDeepSplitFin8Atom175 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1415 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom176 χ ∧
      ¬HalfPureDeepSplitFin8Atom106 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom106 HalfPureDeepSplitFin8Atom176 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1421 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom177 χ ∧
      ¬HalfPureDeepSplitFin8Atom107 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom107 HalfPureDeepSplitFin8Atom177 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1427 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom178 χ ∧
      ¬HalfPureDeepSplitFin8Atom108 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom108 HalfPureDeepSplitFin8Atom178 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1433 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom179 χ ∧
      ¬HalfPureDeepSplitFin8Atom109 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom109 HalfPureDeepSplitFin8Atom179 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1434 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom179 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom179 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1439 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom180 χ ∧
      ¬HalfPureDeepSplitFin8Atom110 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom110 HalfPureDeepSplitFin8Atom180 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1445 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom181 χ ∧
      ¬HalfPureDeepSplitFin8Atom111 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom111 HalfPureDeepSplitFin8Atom181 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1451 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom182 χ ∧
      ¬HalfPureDeepSplitFin8Atom112 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom112 HalfPureDeepSplitFin8Atom182 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1457 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom183 χ ∧
      ¬HalfPureDeepSplitFin8Atom113 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom113 HalfPureDeepSplitFin8Atom183 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
