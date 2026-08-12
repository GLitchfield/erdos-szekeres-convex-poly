module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 0. -/

theorem halfPureSingletonFanFin10_clause00697 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00698 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00699 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00700 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00701 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00702 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00703 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00704 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00705 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00706 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00708 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00712 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00713 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00717 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00719 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00720 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0150 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00721 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00722 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00723 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00724 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00725 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00726 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00727 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00728 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00729 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00730 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00732 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00736 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00737 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00741 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00743 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00744 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0151 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
