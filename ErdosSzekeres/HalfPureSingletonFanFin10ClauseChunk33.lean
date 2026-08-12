module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 33. -/

theorem halfPureSingletonFanFin10_clause04476 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04480 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04481 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04485 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04487 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04488 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04489 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04490 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04491 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04492 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04493 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04494 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04495 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04496 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04497 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04498 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04500 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04501 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04504 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04505 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04509 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04511 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04512 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0308 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04513 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04514 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04515 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04516 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04517 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04518 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04519 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04520 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04522 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0309 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
