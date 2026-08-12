module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 2. -/

theorem halfPureSingletonFanFin10_clause00804 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00808 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00809 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00813 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00815 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00816 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0154 at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00937 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00938 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00939 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00940 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00941 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00942 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00943 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00944 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00945 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00946 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00948 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00952 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00953 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00957 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00958 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00959 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00960 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0160 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00961 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0077 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00962 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0077 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00966 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0077 at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause00985 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ) := by
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

theorem halfPureSingletonFanFin10_clause00986 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ) := by
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

theorem halfPureSingletonFanFin10_clause00987 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
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

theorem halfPureSingletonFanFin10_clause00988 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ) := by
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

theorem halfPureSingletonFanFin10_clause00989 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
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

theorem halfPureSingletonFanFin10_clause00990 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ) := by
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

end ErdosSzekeres

end
