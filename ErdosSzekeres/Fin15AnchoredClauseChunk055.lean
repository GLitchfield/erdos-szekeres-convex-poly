module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 055. -/

theorem fin15Anchored_clause07040 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07041 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07042 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07043 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07044 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07045 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07046 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07047 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07048 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07049 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07050 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07051 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07052 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07053 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07054 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07055 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07056 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07057 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07058 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07059 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07060 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07061 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07062 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07063 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07064 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07065 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07066 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07067 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07068 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07069 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07070 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07071 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 10) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07096 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07097 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07098 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07099 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07100 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 11) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0002 Fin15AnchoredAtom0014
    Fin15AnchoredAtom0092 Fin15AnchoredAtom0456 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0014 chi ∧
      Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0002 Fin15AnchoredAtom0014
    Fin15AnchoredAtom0092 Fin15AnchoredAtom0456 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0003 Fin15AnchoredAtom0015
    Fin15AnchoredAtom0093 Fin15AnchoredAtom0457 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0003 Fin15AnchoredAtom0015
    Fin15AnchoredAtom0093 Fin15AnchoredAtom0457 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0004 Fin15AnchoredAtom0016
    Fin15AnchoredAtom0094 Fin15AnchoredAtom0458 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07106 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0004 Fin15AnchoredAtom0016
    Fin15AnchoredAtom0094 Fin15AnchoredAtom0458 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0005 Fin15AnchoredAtom0017
    Fin15AnchoredAtom0095 Fin15AnchoredAtom0459 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0005 Fin15AnchoredAtom0017
    Fin15AnchoredAtom0095 Fin15AnchoredAtom0459 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07109 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0006 Fin15AnchoredAtom0018
    Fin15AnchoredAtom0096 Fin15AnchoredAtom0460 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07110 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0006 Fin15AnchoredAtom0018
    Fin15AnchoredAtom0096 Fin15AnchoredAtom0460 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0007 Fin15AnchoredAtom0019
    Fin15AnchoredAtom0097 Fin15AnchoredAtom0461 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0007 Fin15AnchoredAtom0019
    Fin15AnchoredAtom0097 Fin15AnchoredAtom0461 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0008 Fin15AnchoredAtom0020
    Fin15AnchoredAtom0098 Fin15AnchoredAtom0462 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0008 Fin15AnchoredAtom0020
    Fin15AnchoredAtom0098 Fin15AnchoredAtom0462 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0009 Fin15AnchoredAtom0021
    Fin15AnchoredAtom0099 Fin15AnchoredAtom0463 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0009 Fin15AnchoredAtom0021
    Fin15AnchoredAtom0099 Fin15AnchoredAtom0463 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07117 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0010 Fin15AnchoredAtom0022
    Fin15AnchoredAtom0100 Fin15AnchoredAtom0464 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07118 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0010 Fin15AnchoredAtom0022
    Fin15AnchoredAtom0100 Fin15AnchoredAtom0464 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0011 Fin15AnchoredAtom0023
    Fin15AnchoredAtom0101 Fin15AnchoredAtom0465 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0011 Fin15AnchoredAtom0023
    Fin15AnchoredAtom0101 Fin15AnchoredAtom0465 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0012 Fin15AnchoredAtom0024
    Fin15AnchoredAtom0102 Fin15AnchoredAtom0466 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0012 Fin15AnchoredAtom0024
    Fin15AnchoredAtom0102 Fin15AnchoredAtom0466 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0013 Fin15AnchoredAtom0025
    Fin15AnchoredAtom0103 Fin15AnchoredAtom0467 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0001 Fin15AnchoredAtom0013 Fin15AnchoredAtom0025
    Fin15AnchoredAtom0103 Fin15AnchoredAtom0467 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0003 Fin15AnchoredAtom0026
    Fin15AnchoredAtom0104 Fin15AnchoredAtom0468 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0003 Fin15AnchoredAtom0026
    Fin15AnchoredAtom0104 Fin15AnchoredAtom0468 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0004 Fin15AnchoredAtom0027
    Fin15AnchoredAtom0105 Fin15AnchoredAtom0469 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07128 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0004 Fin15AnchoredAtom0027
    Fin15AnchoredAtom0105 Fin15AnchoredAtom0469 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07129 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0005 Fin15AnchoredAtom0028
    Fin15AnchoredAtom0106 Fin15AnchoredAtom0470 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0005 Fin15AnchoredAtom0028
    Fin15AnchoredAtom0106 Fin15AnchoredAtom0470 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0006 Fin15AnchoredAtom0029
    Fin15AnchoredAtom0107 Fin15AnchoredAtom0471 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0006 Fin15AnchoredAtom0029
    Fin15AnchoredAtom0107 Fin15AnchoredAtom0471 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0007 Fin15AnchoredAtom0030
    Fin15AnchoredAtom0108 Fin15AnchoredAtom0472 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0007 Fin15AnchoredAtom0030
    Fin15AnchoredAtom0108 Fin15AnchoredAtom0472 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0008 Fin15AnchoredAtom0031
    Fin15AnchoredAtom0109 Fin15AnchoredAtom0473 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0008 Fin15AnchoredAtom0031
    Fin15AnchoredAtom0109 Fin15AnchoredAtom0473 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0009 Fin15AnchoredAtom0032
    Fin15AnchoredAtom0110 Fin15AnchoredAtom0474 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07138 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0009 Fin15AnchoredAtom0032
    Fin15AnchoredAtom0110 Fin15AnchoredAtom0474 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0010 Fin15AnchoredAtom0033
    Fin15AnchoredAtom0111 Fin15AnchoredAtom0475 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07140 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0010 Fin15AnchoredAtom0033
    Fin15AnchoredAtom0111 Fin15AnchoredAtom0475 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0011 Fin15AnchoredAtom0034
    Fin15AnchoredAtom0112 Fin15AnchoredAtom0476 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0011 Fin15AnchoredAtom0034
    Fin15AnchoredAtom0112 Fin15AnchoredAtom0476 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0012 Fin15AnchoredAtom0035
    Fin15AnchoredAtom0113 Fin15AnchoredAtom0477 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0012 Fin15AnchoredAtom0035
    Fin15AnchoredAtom0113 Fin15AnchoredAtom0477 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0013 Fin15AnchoredAtom0036
    Fin15AnchoredAtom0114 Fin15AnchoredAtom0478 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07146 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0002 Fin15AnchoredAtom0013 Fin15AnchoredAtom0036
    Fin15AnchoredAtom0114 Fin15AnchoredAtom0478 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07147 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0004 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0115 Fin15AnchoredAtom0479 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07148 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0004 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0115 Fin15AnchoredAtom0479 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0005 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0116 Fin15AnchoredAtom0480 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0005 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0116 Fin15AnchoredAtom0480 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0006 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0117 Fin15AnchoredAtom0481 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0006 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0117 Fin15AnchoredAtom0481 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0007 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0118 Fin15AnchoredAtom0482 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0007 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0118 Fin15AnchoredAtom0482 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0008 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0119 Fin15AnchoredAtom0483 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0008 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0119 Fin15AnchoredAtom0483 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07157 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0009 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0120 Fin15AnchoredAtom0484 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07158 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0009 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0120 Fin15AnchoredAtom0484 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07159 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0010 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0121 Fin15AnchoredAtom0485 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0010 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0121 Fin15AnchoredAtom0485 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0011 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0122 Fin15AnchoredAtom0486 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0011 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0122 Fin15AnchoredAtom0486 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07163 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0012 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0123 Fin15AnchoredAtom0487 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0012 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0123 Fin15AnchoredAtom0487 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0013 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0124 Fin15AnchoredAtom0488 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0003 Fin15AnchoredAtom0013 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0124 Fin15AnchoredAtom0488 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07167 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0005 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0125 Fin15AnchoredAtom0489 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
