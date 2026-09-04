module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 050. -/

theorem fin15Anchored_clause06400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06456 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06457 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06458 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06459 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06460 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06461 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06462 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06463 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06464 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06465 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06466 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06467 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06468 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06469 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06470 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06471 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06472 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06473 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06474 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06475 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06476 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06477 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06478 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06479 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06480 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06481 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06482 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06483 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06484 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06485 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06486 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06487 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06488 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06489 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06490 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06491 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06492 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06493 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06494 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06495 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06496 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06497 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06498 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06499 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06500 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06501 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06502 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06503 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06504 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06505 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06506 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06507 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06508 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06509 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06510 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06511 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
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

theorem fin15Anchored_clause06522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
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

theorem fin15Anchored_clause06523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
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

theorem fin15Anchored_clause06524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
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

theorem fin15Anchored_clause06525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
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

theorem fin15Anchored_clause06526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
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

theorem fin15Anchored_clause06527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
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

end ErdosSzekeres

end
