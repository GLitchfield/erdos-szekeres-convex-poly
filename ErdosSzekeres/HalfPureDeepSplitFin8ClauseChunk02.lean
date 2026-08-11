module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 2. -/

theorem halfPureDeepSplitFin8_clause0404 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom052 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0406 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom052 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0407 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom052 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0410 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom032 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom053 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0418 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom054 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0422 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom054 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0423 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom054 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0426 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom032 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom032 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0431 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom032 HalfPureDeepSplitFin8Atom033 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom055 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0434 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0435 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0436 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0437 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0438 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0439 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0440 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0441 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0442 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0443 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0444 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0446 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0447 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      HalfPureDeepSplitFin8Atom041 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom041
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0449 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
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

theorem halfPureDeepSplitFin8_clause0450 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom037 χ ∧
      HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
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

end ErdosSzekeres

end
