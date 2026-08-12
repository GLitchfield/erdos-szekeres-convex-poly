module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 11. -/

theorem halfPureSingletonFanFin10_clause01847 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01848 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01849 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01850 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01853 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01855 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01860 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0198 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0198 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01869 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0198 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0198 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01872 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0198 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0198 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01873 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01874 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01875 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01876 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01877 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01878 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01879 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01880 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01897 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01898 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01899 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01900 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01901 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01902 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01903 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01904 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01905 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
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

theorem halfPureSingletonFanFin10_clause01906 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
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

theorem halfPureSingletonFanFin10_clause01907 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
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

theorem halfPureSingletonFanFin10_clause01908 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
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

theorem halfPureSingletonFanFin10_clause01909 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
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

theorem halfPureSingletonFanFin10_clause01912 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
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

theorem halfPureSingletonFanFin10_clause01913 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
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

end ErdosSzekeres

end
