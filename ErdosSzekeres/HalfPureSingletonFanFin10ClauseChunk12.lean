module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 12. -/

theorem halfPureSingletonFanFin10_clause01914 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0200 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01915 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0200 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01917 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0200 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01919 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0200 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01920 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0200 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01921 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01922 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01923 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01924 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01925 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01926 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01927 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01928 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01930 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01936 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01937 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01941 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01943 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01944 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0201 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01945 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01946 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01947 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01948 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01949 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01950 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01951 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01952 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01954 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0202 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01961 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0202 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01967 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0202 at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01969 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01970 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
