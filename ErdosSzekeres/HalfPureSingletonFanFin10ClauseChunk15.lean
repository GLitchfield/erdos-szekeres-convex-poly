module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 15. -/

theorem halfPureSingletonFanFin10_clause03456 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03457 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03458 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03459 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03460 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03461 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03462 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03463 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03464 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03466 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03468 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03472 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03473 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03477 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03479 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0265 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03481 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03482 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03483 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03484 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03485 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03486 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03487 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03488 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03489 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03490 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03492 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03496 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03497 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03499 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03501 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03503 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03504 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0266 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
