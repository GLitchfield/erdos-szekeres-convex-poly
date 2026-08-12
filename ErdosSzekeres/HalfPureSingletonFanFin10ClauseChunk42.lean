module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 42. -/

theorem halfPureSingletonFanFin10_clause05017 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05018 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05019 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05020 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05021 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05022 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05023 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05024 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05025 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05026 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05032 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05033 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05037 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05039 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0330 at hbad
  cases hcolor0 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06871 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0392 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0392 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06872 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0392 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0392 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06873 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0392 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0392 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06874 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0392 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0392 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06875 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0392 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0392 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06877 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0644 χ ∧
      ¬HalfPureSingletonFanFin10Atom0392 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0392 HalfPureSingletonFanFin10Atom0644 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109, halfPureSingletonFanFin10_cupSet_iff_mask0109] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06889 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0896 χ ∧
      ¬HalfPureSingletonFanFin10Atom0392 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0392 HalfPureSingletonFanFin10Atom0896 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109, halfPureSingletonFanFin10_capSet_iff_mask0109] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06890 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0896 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0017
    HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0896 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0109, halfPureSingletonFanFin10_capSet_iff_mask0109] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06903 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0393 χ ∧
      ¬HalfPureSingletonFanFin10Atom0161 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0393 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0173] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06904 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0393 χ ∧
      ¬HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0393 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0173] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06905 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0393 χ ∧
      ¬HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0393 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0173] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06907 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0645 χ ∧
      ¬HalfPureSingletonFanFin10Atom0393 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0393 HalfPureSingletonFanFin10Atom0645 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0173, halfPureSingletonFanFin10_cupSet_iff_mask0173] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06919 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0897 χ ∧
      ¬HalfPureSingletonFanFin10Atom0393 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0393 HalfPureSingletonFanFin10Atom0897 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0173, halfPureSingletonFanFin10_capSet_iff_mask0173] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06931 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0394 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0394 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06932 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0394 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0394 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06933 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0394 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0394 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06934 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0394 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0394 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06935 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0394 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0394 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301] at hbad
  tauto

end ErdosSzekeres

end
