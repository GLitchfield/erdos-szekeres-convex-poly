module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 40. -/

theorem halfPureSingletonFanFin10_clause04906 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04907 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04909 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04912 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04913 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04917 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04919 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0325 at hbad
  cases hcolor0 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04921 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04922 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04923 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04924 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04925 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04926 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04927 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04928 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04930 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0326 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04932 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0326 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04936 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0326 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04937 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0326 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04941 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0326 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04945 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04946 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04947 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04948 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04949 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04950 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04951 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04952 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04954 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0327 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04956 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0327 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04961 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0327 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04964 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0327 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
