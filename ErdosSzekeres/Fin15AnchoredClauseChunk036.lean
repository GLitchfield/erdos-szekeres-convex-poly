module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 036. -/

theorem fin15Anchored_clause04608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
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

theorem fin15Anchored_clause04609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
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

theorem fin15Anchored_clause04610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
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

theorem fin15Anchored_clause04611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
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

theorem fin15Anchored_clause04612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04664 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04665 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04666 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04667 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04668 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04669 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04670 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04671 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04672 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04673 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04674 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04675 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04676 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04677 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04678 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04679 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04680 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04681 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04682 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04683 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04684 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04685 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04686 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04687 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04688 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04689 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04690 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04691 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04692 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04693 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04694 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04695 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04696 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04697 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04698 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04699 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04700 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04701 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04702 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04703 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04704 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04705 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04706 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04707 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04708 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04709 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04710 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04711 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04712 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04713 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04714 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04715 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04716 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04717 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04718 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04719 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04720 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04721 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04722 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04723 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04724 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04725 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04726 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04727 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04728 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04729 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04730 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04731 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04732 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04733 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04734 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04735 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
