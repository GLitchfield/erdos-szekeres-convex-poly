module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 035. -/

theorem fin15Anchored_clause04480 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04481 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04482 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04483 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04484 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04485 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04486 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04487 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04488 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04489 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04490 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04491 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04492 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04493 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04494 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04495 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04496 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04497 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04498 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04499 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04500 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04501 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04502 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04503 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04504 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04505 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04506 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04507 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04508 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04509 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04510 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04511 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0268 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0268 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0268 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
