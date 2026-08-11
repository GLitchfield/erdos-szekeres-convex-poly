module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 6. -/

theorem halfPureDeepSplitFin8_clause0539 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0540 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0541 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0542 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0543 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0544 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom048 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0545 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0546 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0547 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0548 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0549 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0550 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0551 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0552 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom050 χ ∧
      HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0553 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0554 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0555 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0556 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0558 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0559 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom053 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0560 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom053 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom055
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0859 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom094 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom094 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0875 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom096 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom096 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0915 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom101 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom101 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
