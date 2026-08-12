module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 36. -/

theorem halfPureSingletonFanFin10_clause04633 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04634 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04635 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04636 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04637 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04638 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04639 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04640 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04641 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04642 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04644 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04648 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04649 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04651 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04653 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04655 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04656 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0314 at hbad
  cases hcolor0 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04657 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04658 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04659 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04660 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04661 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04662 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04663 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04664 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04666 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04667 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04669 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04672 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04673 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04677 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04679 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0315 at hbad
  cases hcolor0 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
