module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 6. -/

theorem halfPureSingletonFanFin10_clause01169 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01171 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01173 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01175 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01176 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0015
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0169 at hbad
  cases hcolor0 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01297 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01298 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01299 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01300 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01301 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01302 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01303 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01304 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01305 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01306 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01308 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01312 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01313 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01317 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01319 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01320 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0175 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01326 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0092 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01336 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0176 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01337 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0019
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0176 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01345 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01346 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01347 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01348 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01349 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01350 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01351 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01352 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0093 at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
