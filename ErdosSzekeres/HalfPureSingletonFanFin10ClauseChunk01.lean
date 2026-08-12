module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 1. -/

theorem halfPureSingletonFanFin10_clause00747 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00750 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00752 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00756 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0152 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00761 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0152 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00765 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0152 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00769 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00770 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00771 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00772 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00773 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00774 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00775 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00776 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00777 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00778 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00780 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00784 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00785 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00789 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00791 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00792 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0153 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00793 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00794 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00795 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00796 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00797 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00798 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00799 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00800 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00801 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00802 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
