module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 13. -/

theorem halfPureSingletonFanFin10_clause01971 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01972 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01973 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01974 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01975 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01976 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01977 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01978 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01980 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01984 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01985 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01989 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01991 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01992 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0203 at hbad
  cases hcolor0 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01994 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01995 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01996 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01997 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01998 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01999 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause02008 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      HalfPureSingletonFanFin10Atom0204 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0034 HalfPureSingletonFanFin10Atom0035
    HalfPureSingletonFanFin10Atom0036 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0204 at hbad
  cases hcolor0 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03361 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03363 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03364 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03366 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03367 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03368 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03372 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086
    HalfPureSingletonFanFin10Atom0261 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03376 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086
    HalfPureSingletonFanFin10Atom0261 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03377 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0066
    HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0086
    HalfPureSingletonFanFin10Atom0261 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03385 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
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

theorem halfPureSingletonFanFin10_clause03386 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
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

end ErdosSzekeres

end
