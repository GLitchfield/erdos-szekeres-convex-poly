module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 22. -/

theorem halfPureSingletonFanFin10_clause03846 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03847 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03848 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03851 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03856 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03857 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03861 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03862 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03863 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03864 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0281 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03865 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03866 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03867 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03868 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03869 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03870 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03871 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03872 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03877 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0282 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0282 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03885 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0282 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0282 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03889 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03890 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03891 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03892 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03894 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03895 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03896 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03905 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0283 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03909 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0283 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03911 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0283 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03913 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03914 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
