module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 9. -/

theorem halfPureSingletonFanFin10_clause01463 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0181 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01464 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0181 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01465 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01466 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01469 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01471 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01472 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01473 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0182 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0182 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01476 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0182 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0182 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01488 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0182 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0182 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01489 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0099 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01490 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0099 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01491 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0099 at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01513 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01514 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01515 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01516 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01517 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01518 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01519 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01520 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01522 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01524 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01528 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01529 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01533 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01535 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01536 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0184 at hbad
  cases hcolor0 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01777 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0028
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01778 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0028
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01782 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0028
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01783 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0028
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
