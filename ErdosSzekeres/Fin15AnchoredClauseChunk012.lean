module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 012. -/

theorem fin15Anchored_clause01536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
