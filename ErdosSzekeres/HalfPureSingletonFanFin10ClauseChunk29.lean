module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 29. -/

theorem halfPureSingletonFanFin10_clause04250 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
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

theorem halfPureSingletonFanFin10_clause04251 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
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

theorem halfPureSingletonFanFin10_clause04252 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
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

theorem halfPureSingletonFanFin10_clause04253 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
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

theorem halfPureSingletonFanFin10_clause04254 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
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

theorem halfPureSingletonFanFin10_clause04255 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
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

theorem halfPureSingletonFanFin10_clause04256 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
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

theorem halfPureSingletonFanFin10_clause04258 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04260 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04264 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04265 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04269 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04271 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04272 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0298 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04273 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04274 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04275 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04276 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04277 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04278 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04279 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04280 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04282 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0299 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04284 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0299 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04288 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0299 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04289 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0299 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04295 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0299 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04297 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04298 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04299 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04300 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04302 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
