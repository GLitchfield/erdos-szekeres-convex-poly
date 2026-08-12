module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 39. -/

theorem halfPureSingletonFanFin10_clause04831 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
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

theorem halfPureSingletonFanFin10_clause04832 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
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

theorem halfPureSingletonFanFin10_clause04836 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0322 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04841 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0322 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04845 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0322 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04847 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0322 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04849 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04851 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04853 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04854 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04855 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04856 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04865 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0323 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0323 at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04873 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04874 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04875 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04876 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04877 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04878 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04879 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04880 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04881 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0324 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04882 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0324 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04895 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0324 at hbad
  cases hcolor0 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04897 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04898 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04899 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04900 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04901 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04902 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04903 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04904 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
