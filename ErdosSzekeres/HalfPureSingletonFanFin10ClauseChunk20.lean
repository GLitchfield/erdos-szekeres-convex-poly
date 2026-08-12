module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 20. -/

theorem halfPureSingletonFanFin10_clause03704 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03705 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03706 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03707 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03708 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03709 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03711 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03712 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03713 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03717 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03719 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03720 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0275 at hbad
  cases hcolor0 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03721 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03724 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03726 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03727 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03737 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0276 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03743 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0276 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03744 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0276 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03745 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03746 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03747 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03748 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03750 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03751 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03752 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03760 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0277 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03767 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0277 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03768 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0277 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03769 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03770 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03771 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
