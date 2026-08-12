module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 14. -/

theorem halfPureSingletonFanFin10_clause03387 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03388 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03389 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03391 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03392 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03396 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0262 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03399 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0262 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03407 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0262 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03408 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0262 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03409 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03410 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03411 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03412 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03414 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03416 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03418 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0263 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03420 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0263 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03424 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0263 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03433 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03434 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03435 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03436 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03437 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03438 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03439 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03440 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03442 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03444 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
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

theorem halfPureSingletonFanFin10_clause03447 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03448 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03449 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03455 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0264 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
