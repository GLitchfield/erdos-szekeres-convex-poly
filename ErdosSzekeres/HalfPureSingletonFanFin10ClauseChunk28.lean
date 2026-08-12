module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 28. -/

theorem halfPureSingletonFanFin10_clause04181 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
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

theorem halfPureSingletonFanFin10_clause04182 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
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

theorem halfPureSingletonFanFin10_clause04183 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
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

theorem halfPureSingletonFanFin10_clause04184 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
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

theorem halfPureSingletonFanFin10_clause04186 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04192 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04193 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04194 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04196 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04197 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04199 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0295 at hbad
  cases hcolor0 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04201 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04202 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04204 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04205 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04206 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04207 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04208 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04212 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0296 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04216 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0296 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04221 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0296 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04223 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0101
    HalfPureSingletonFanFin10Atom0296 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04225 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04228 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04230 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04231 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04232 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04236 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0297 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0297 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04245 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0297 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0297 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04247 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0297 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0297 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04248 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0297 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0297 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04249 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
