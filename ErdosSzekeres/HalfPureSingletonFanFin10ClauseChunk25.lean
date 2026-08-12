module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 25. -/

theorem halfPureSingletonFanFin10_clause04025 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0288 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04028 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0288 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04029 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0288 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04031 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0288 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04033 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04034 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04035 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04036 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04037 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04038 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04039 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04040 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04042 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04044 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04047 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04048 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04049 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04053 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04055 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0289 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04057 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04058 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04060 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04061 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04062 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04063 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04064 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04066 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0290 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04073 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0290 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04074 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0290 at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04081 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04082 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04083 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
