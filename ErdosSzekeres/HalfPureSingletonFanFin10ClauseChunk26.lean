module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 26. -/

theorem halfPureSingletonFanFin10_clause04084 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04085 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04086 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04087 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04088 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04089 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04090 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04092 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04096 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04097 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04100 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04101 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04103 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04104 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0291 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04105 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04106 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04107 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04108 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04109 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04110 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04111 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04112 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04114 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04117 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04120 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04121 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04125 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04127 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0292 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04129 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04130 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04131 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04132 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
