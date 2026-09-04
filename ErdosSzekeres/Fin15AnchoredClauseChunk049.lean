module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 049. -/

theorem fin15Anchored_clause06272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
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

theorem fin15Anchored_clause06397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
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

theorem fin15Anchored_clause06398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
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

theorem fin15Anchored_clause06399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
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

end ErdosSzekeres

end
