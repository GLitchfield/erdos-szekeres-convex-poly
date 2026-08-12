module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 18. -/

theorem halfPureSingletonFanFin10_clause03605 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03606 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03607 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03608 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03609 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03610 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03612 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03616 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03617 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03621 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03623 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03624 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0271 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03625 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03626 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03627 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03628 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03629 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03630 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03631 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03632 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03633 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03634 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03636 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03640 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03641 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03645 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03646 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03647 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03648 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0272 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03649 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03650 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03651 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
