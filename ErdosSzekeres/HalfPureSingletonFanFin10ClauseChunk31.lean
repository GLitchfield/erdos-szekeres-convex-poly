module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 31. -/

theorem halfPureSingletonFanFin10_clause04372 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
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

theorem halfPureSingletonFanFin10_clause04373 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
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

theorem halfPureSingletonFanFin10_clause04374 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
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

theorem halfPureSingletonFanFin10_clause04375 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
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

theorem halfPureSingletonFanFin10_clause04376 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
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

theorem halfPureSingletonFanFin10_clause04377 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04378 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04379 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04380 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04384 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04385 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04389 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04391 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04392 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom0303 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04393 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04394 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04395 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04396 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04397 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04398 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04399 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04400 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04408 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0304 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04409 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0304 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04415 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0304 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04416 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0304 at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04417 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04418 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04419 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04420 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04421 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04422 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
