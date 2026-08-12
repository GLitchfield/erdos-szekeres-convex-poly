module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 38. -/

theorem halfPureSingletonFanFin10_clause04754 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04755 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04756 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04757 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04758 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04759 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04760 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04764 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0319 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04769 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0319 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04773 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0319 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04777 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04778 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04781 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0115 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04792 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0320 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0320 at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04801 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04802 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04803 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04804 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04805 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04806 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04807 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04808 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04810 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0321 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04816 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0321 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04817 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0321 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04821 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0321 at hbad
  cases hcolor0 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04825 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04826 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04827 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04828 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04829 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04830 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
