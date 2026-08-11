module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 1. -/

theorem halfPureDeepSplitFin8_clause0376 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      HalfPureDeepSplitFin8Atom048 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom032
    HalfPureDeepSplitFin8Atom048 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0377 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0378 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0379 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0380 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0382 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom033 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0384 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom033 χ ∧
      HalfPureDeepSplitFin8Atom049 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom033
    HalfPureDeepSplitFin8Atom049 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0385 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0386 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0388 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0389 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0390 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0391 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0392 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom050 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0393 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0394 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0395 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0396 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0397 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0398 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0399 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0400 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom051 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0401 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom029 χ ∧
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

theorem halfPureDeepSplitFin8_clause0402 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
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

end ErdosSzekeres

end
