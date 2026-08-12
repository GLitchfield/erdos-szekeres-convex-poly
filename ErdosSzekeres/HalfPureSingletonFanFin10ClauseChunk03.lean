module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 3. -/

theorem halfPureSingletonFanFin10_clause00991 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00992 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00993 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00994 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00996 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01000 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01001 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01005 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01007 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01008 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0162 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01009 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01011 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01012 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01013 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01014 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01015 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01016 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01017 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01018 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01020 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01024 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01025 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01029 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01031 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01032 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0163 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01033 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01034 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01037 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01038 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01039 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01040 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0080 at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01044 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
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

end ErdosSzekeres

end
