module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 23. -/

theorem halfPureSingletonFanFin10_clause03915 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03917 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03918 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03919 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03920 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03936 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0284 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0284 at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03937 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03938 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03939 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03940 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03941 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03942 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03943 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03944 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03946 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0285 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03952 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0285 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03953 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0285 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03957 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0285 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03959 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0285 at hbad
  cases hcolor0 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03961 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03962 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03963 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03964 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03965 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03966 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03967 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03968 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03972 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0286 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03976 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0286 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03977 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0286 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03981 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0286 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03983 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0286 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
