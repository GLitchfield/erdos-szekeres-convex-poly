module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 004. -/

theorem fin15Anchored_clause00512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
