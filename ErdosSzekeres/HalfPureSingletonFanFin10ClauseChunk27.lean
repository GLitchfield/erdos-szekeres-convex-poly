module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 27. -/

theorem halfPureSingletonFanFin10_clause04133 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04134 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04135 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04136 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04138 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04139 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04144 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04145 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04148 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04151 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0293 at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04153 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04154 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04155 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04156 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04157 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04158 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04159 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04160 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04161 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04162 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04164 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04166 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04168 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04169 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04171 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04173 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04175 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04176 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0294 at hbad
  cases hcolor0 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04177 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04178 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04179 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04180 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
