module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 16. -/

theorem halfPureSingletonFanFin10_clause03505 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03507 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03509 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03510 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03511 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03512 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03514 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0267 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03516 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0267 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03520 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0267 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03521 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0267 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03527 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0267 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03529 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03530 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03531 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03532 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03533 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03534 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03535 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03536 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03537 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03538 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03540 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03544 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03545 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03549 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03551 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03552 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0268 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03553 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03554 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03555 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03556 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03557 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
