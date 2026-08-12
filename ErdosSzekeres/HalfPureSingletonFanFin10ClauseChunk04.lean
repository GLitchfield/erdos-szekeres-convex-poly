module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 4. -/

theorem halfPureSingletonFanFin10_clause01049 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0164 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01053 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0164 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01055 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0164 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01057 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01058 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01059 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01060 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01061 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01062 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01063 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01064 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01065 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01066 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01068 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01072 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01073 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01077 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01079 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01080 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0165 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01081 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01082 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01083 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01084 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01085 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01086 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01087 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01088 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01089 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01090 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01092 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01094 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01096 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0166 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
