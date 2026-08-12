module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 7. -/

theorem halfPureSingletonFanFin10_clause01353 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01354 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01356 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01360 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01361 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01365 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01367 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01368 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0177 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01369 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01370 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01371 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01372 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01373 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01374 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01375 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01376 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01377 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01378 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01380 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01384 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01385 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01389 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01390 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01391 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01392 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0021
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0178 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01393 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01394 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01396 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01397 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01398 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01399 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01400 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
