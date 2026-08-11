module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 0. -/

theorem halfPureDeepSplitFin8_clause0287 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom037 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom023 HalfPureDeepSplitFin8Atom027
    HalfPureDeepSplitFin8Atom037 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0290 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom028
    HalfPureDeepSplitFin8Atom038 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0293 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom038 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom028
    HalfPureDeepSplitFin8Atom038 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0295 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom038 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom028
    HalfPureDeepSplitFin8Atom038 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0298 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom029
    HalfPureDeepSplitFin8Atom039 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0306 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom022 χ ∧
      HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom030
    HalfPureDeepSplitFin8Atom040 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0311 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom022 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom030 χ ∧
      HalfPureDeepSplitFin8Atom040 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom022 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom030
    HalfPureDeepSplitFin8Atom040 at hbad
  cases hcolor0 : χ ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0320 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom041 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom023 HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom031
    HalfPureDeepSplitFin8Atom041 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0322 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom023 χ ∧
      HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom023 HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom032
    HalfPureDeepSplitFin8Atom042 at hbad
  cases hcolor0 : χ ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0338 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom044 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0343 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom025 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom044 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom034
    HalfPureDeepSplitFin8Atom044 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0346 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom024 χ ∧
      HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom045 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0351 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom024 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom045 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom024 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom035
    HalfPureDeepSplitFin8Atom045 at hbad
  cases hcolor0 : χ ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0354 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom025 χ ∧
      HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom046 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0359 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom025 χ ∧
      ¬HalfPureDeepSplitFin8Atom026 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom046 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom046 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0360 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom025 χ ∧
      HalfPureDeepSplitFin8Atom026 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom046 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom025 HalfPureDeepSplitFin8Atom026 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom046 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0361 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom031
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0365 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom031
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0367 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom031
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0368 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom031 χ ∧
      HalfPureDeepSplitFin8Atom047 χ) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom031
    HalfPureDeepSplitFin8Atom047 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0369 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
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

theorem halfPureDeepSplitFin8_clause0370 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
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

theorem halfPureDeepSplitFin8_clause0372 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
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

theorem halfPureDeepSplitFin8_clause0374 (χ : TripleColoring 8)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ ∧
      HalfPureDeepSplitFin8Atom032 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ) := by
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

end ErdosSzekeres

end
