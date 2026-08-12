module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 24. -/

theorem halfPureSingletonFanFin10_clause03984 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
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

theorem halfPureSingletonFanFin10_clause03985 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03986 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03987 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03988 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03989 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03990 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03991 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03992 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03993 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03994 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03995 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03996 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04000 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04001 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04002 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04005 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04006 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04007 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04008 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0287 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04009 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04010 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04011 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04012 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04013 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04014 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04015 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04016 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04017 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
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

theorem halfPureSingletonFanFin10_clause04018 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
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

theorem halfPureSingletonFanFin10_clause04020 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
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

theorem halfPureSingletonFanFin10_clause04024 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
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

end ErdosSzekeres

end
