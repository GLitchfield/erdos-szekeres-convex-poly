module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 34. -/

theorem halfPureSingletonFanFin10_clause04523 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
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

theorem halfPureSingletonFanFin10_clause04524 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0309 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04529 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
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

theorem halfPureSingletonFanFin10_clause04533 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0309 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04536 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0309 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04537 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04539 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04540 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04541 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04542 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04543 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04544 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04546 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04548 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04549 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04552 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04553 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04559 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0310 at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04561 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04562 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04563 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04564 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04565 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04566 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04567 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04568 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04569 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
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

theorem halfPureSingletonFanFin10_clause04570 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
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

theorem halfPureSingletonFanFin10_clause04571 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
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

theorem halfPureSingletonFanFin10_clause04572 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
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

theorem halfPureSingletonFanFin10_clause04576 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
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

theorem halfPureSingletonFanFin10_clause04577 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
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

end ErdosSzekeres

end
