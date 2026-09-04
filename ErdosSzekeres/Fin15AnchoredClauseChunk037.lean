module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 037. -/

theorem fin15Anchored_clause04736 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
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

theorem fin15Anchored_clause04737 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
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

theorem fin15Anchored_clause04738 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
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

theorem fin15Anchored_clause04739 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0278 chi ∧
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

theorem fin15Anchored_clause04740 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04741 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04742 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04743 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04744 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04745 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04746 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04747 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04748 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04749 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04750 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04751 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04752 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04753 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04754 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04755 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04756 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04757 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04758 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04759 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04768 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04769 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04770 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04771 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04772 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04773 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04774 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04775 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04776 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04777 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04778 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04779 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04780 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04781 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04782 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04783 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04784 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04785 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04786 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04787 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04788 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04789 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04790 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04791 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04792 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04793 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04794 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04795 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04796 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04797 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04798 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04799 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04800 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04801 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04802 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04803 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04804 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04805 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04806 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04807 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04808 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04809 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04810 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04811 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04812 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04813 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04814 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04815 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04816 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04817 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04818 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04819 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04820 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04821 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04822 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04823 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04824 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04825 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04826 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04827 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04828 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04829 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04830 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04831 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04832 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04833 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04834 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04835 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04836 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04837 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04838 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04839 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04840 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04841 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04842 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04843 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04844 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04845 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04846 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04847 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04848 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04849 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04850 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04851 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04852 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04853 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04854 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04855 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04856 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04857 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04858 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04859 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04860 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04861 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04862 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04863 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
