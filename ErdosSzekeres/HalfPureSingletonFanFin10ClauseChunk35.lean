module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 35. -/

theorem halfPureSingletonFanFin10_clause04581 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0311 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04583 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0311 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04584 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0311 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04585 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04586 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04587 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04588 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04589 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04590 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04591 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04592 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04594 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04595 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04596 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04600 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04601 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04605 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04607 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0312 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04609 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04610 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04611 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04612 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04613 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04614 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04615 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04616 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04618 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04620 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04624 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04625 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04628 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04631 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0313 at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
