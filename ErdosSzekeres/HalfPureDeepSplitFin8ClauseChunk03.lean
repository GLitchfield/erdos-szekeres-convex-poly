module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 3. -/

theorem halfPureDeepSplitFin8_clause0451 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0453 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0454 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0455 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0456 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom042
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0457 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0458 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0459 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0460 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0461 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0462 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0463 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0464 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom043
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0466 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0471 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom044 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0473 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0474 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0475 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0476 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0477 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0478 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0479 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0480 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0482 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom039 χ ∧
      HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom052 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
