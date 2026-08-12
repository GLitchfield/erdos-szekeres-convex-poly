module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 10. -/

theorem halfPureSingletonFanFin10_clause01784 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0028
    HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01801 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01802 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01803 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01804 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01805 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01806 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01807 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01808 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01809 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01810 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01812 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01814 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01816 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01817 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01821 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01823 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01824 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0196 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01825 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01826 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01827 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01828 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01829 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01830 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01831 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01832 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01833 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01834 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01836 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01840 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01841 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause01845 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0197 at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
