module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 043. -/

theorem fin15Anchored_clause05504 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05505 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05506 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05507 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05508 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05509 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05510 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05511 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
