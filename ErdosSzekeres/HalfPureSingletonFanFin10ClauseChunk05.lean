module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 5. -/

theorem halfPureSingletonFanFin10_clause01097 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01101 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01103 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01104 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01105 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01106 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01109 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01111 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01112 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01114 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0167 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01127 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0167 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01128 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0167 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01129 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01130 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01131 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01132 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01133 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01135 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01136 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01151 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0168 at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01153 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01154 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01155 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01156 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01157 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01158 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01159 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01160 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01161 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01162 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01164 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01168 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
