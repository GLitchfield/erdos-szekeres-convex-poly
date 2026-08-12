module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 41. -/

theorem halfPureSingletonFanFin10_clause04967 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0327 at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04969 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04970 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04971 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04972 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04973 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04974 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04975 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04976 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04977 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04978 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04979 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04980 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04984 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04985 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04988 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04989 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04991 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04992 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0328 at hbad
  cases hcolor0 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04993 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04994 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04995 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04996 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04997 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04998 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04999 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05000 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05002 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0329 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05008 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0329 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05009 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0329 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05013 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0329 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause05015 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0329 at hbad
  cases hcolor0 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
