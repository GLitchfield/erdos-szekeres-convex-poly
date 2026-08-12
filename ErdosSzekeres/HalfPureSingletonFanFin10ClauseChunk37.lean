module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 37. -/

theorem halfPureSingletonFanFin10_clause04682 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04683 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04684 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04685 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04687 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04688 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04689 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0316 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04696 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0316 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04703 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0316 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04704 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0316 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04705 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04706 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04707 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04708 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04710 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04711 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04713 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0317 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04721 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0317 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04725 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0317 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04728 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0317 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04729 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04730 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04731 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04732 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04733 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04734 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04735 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04736 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04745 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0318 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0318 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04749 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0318 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0318 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04751 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0318 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0318 at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04753 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0102 χ ∧
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

end ErdosSzekeres

end
