module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 8. -/

theorem halfPureSingletonFanFin10_clause01401 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0179 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01416 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0179 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01417 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01418 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01419 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01420 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01421 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01422 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01423 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01424 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01425 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01426 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01428 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01432 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01433 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01437 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01439 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01440 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0180 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01441 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01442 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01443 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01444 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01445 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01446 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01447 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01448 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0097 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01449 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
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

theorem halfPureSingletonFanFin10_clause01450 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
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

theorem halfPureSingletonFanFin10_clause01452 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
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

theorem halfPureSingletonFanFin10_clause01456 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
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

theorem halfPureSingletonFanFin10_clause01457 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
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

theorem halfPureSingletonFanFin10_clause01461 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
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

end ErdosSzekeres

end
