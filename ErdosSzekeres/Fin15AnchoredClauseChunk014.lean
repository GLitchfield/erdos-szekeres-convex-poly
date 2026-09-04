module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 014. -/

theorem fin15Anchored_clause01792 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01793 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01794 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01795 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01796 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01797 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01798 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01799 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01800 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01801 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01802 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01803 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01804 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01805 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01806 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01807 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01808 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01809 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01810 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01811 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01812 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01813 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01814 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01815 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01816 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01817 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01818 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01819 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01820 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01821 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01822 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01823 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01824 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01825 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01826 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01827 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01828 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01829 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01830 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01831 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01832 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01833 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01834 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01835 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01836 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01837 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01838 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01839 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01840 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01841 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01842 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01843 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01844 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01845 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01846 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01847 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01848 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01849 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01850 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01851 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01852 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01853 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01854 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01855 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01856 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01857 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01858 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01859 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01860 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01861 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01862 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01863 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01864 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01865 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01866 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01867 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01868 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01869 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01870 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01871 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01872 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01873 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01874 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01875 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01876 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01877 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01878 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01879 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01880 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01881 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01882 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01883 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01884 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01885 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01886 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01887 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01888 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01889 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01890 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01891 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01892 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01893 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01894 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01895 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01896 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01897 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01898 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01899 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01900 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01901 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01902 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01903 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01904 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01905 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01906 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01907 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01908 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01909 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01910 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01911 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
