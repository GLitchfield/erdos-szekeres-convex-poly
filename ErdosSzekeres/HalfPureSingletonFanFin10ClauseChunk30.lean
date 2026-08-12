module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 30. -/

theorem halfPureSingletonFanFin10_clause04303 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
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

theorem halfPureSingletonFanFin10_clause04304 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
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

theorem halfPureSingletonFanFin10_clause04308 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0300 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04312 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0300 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04317 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0300 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04319 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0300 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04320 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0300 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04321 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04322 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04323 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04324 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04325 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04326 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04327 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04328 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04332 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0301 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04341 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0301 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04343 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0301 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04344 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0301 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04345 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04346 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04347 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04348 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04349 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04350 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04351 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04352 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04360 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0302 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0302 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04365 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0302 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0087 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0302 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04369 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04370 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04371 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
