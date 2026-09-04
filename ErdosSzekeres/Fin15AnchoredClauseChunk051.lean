module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 051. -/

theorem fin15Anchored_clause06528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
