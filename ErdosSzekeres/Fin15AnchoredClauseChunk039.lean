module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 039. -/

theorem fin15Anchored_clause04992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05024 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05025 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05026 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05027 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05028 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05029 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05030 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05031 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05032 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05033 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05034 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05035 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05036 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05037 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05038 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05039 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05040 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05041 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05042 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05043 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05044 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05045 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05046 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05047 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05048 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05049 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05050 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05051 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05052 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05053 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05054 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05055 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05056 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05057 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05058 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05059 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05060 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05061 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05062 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05063 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05064 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05065 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05066 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05067 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05068 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05069 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0299 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0368 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05070 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0299 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0368 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05071 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0299 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0368 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0299 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0368 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05096 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05097 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05098 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05099 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05100 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05101 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05102 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05103 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05104 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05105 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05106 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05107 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05108 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05109 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05110 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05111 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05112 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05113 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05114 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05115 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05116 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05117 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05118 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05119 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
