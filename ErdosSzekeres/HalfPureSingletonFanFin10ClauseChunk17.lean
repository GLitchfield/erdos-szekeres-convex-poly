module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 17. -/

theorem halfPureSingletonFanFin10_clause03558 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03559 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03560 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03561 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03562 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03564 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03568 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03569 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03572 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03573 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03575 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03576 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0269 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03577 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03578 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03579 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03580 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03581 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03582 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03583 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03584 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03585 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03586 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03588 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03592 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03593 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03594 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03599 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03600 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0270 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03601 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03602 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03603 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03604 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
