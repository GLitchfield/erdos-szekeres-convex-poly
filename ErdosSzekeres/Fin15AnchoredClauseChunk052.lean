module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 052. -/

theorem fin15Anchored_clause06656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0394 chi ∧
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

theorem fin15Anchored_clause06657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0395 Fin15AnchoredAtom0396 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0395 Fin15AnchoredAtom0396 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06664 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06665 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06666 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06667 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06668 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06669 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06670 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06671 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06672 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06673 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06674 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06675 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06676 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06677 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06678 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06679 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06680 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06681 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06682 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06683 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06684 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06685 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06686 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06687 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06688 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06689 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06690 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06691 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06692 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06693 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06694 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06695 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06696 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06697 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06698 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06699 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06700 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06701 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06702 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06703 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06704 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06705 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06706 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06707 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06708 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06709 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06710 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06711 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06712 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06713 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06714 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06715 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06716 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06717 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06718 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06719 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06720 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06721 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06722 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06723 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06724 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06725 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06726 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06727 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06728 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06729 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06730 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06731 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06732 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06733 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06734 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06735 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06736 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06737 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06738 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06739 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06740 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06741 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06742 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06743 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06744 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06745 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06746 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06747 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06748 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06749 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06750 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06751 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06752 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06753 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06754 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06755 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06756 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06757 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06758 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06759 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06768 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06769 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06770 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06771 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06772 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06773 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06774 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06775 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06776 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06777 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06778 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06779 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06780 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06781 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06782 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06783 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
