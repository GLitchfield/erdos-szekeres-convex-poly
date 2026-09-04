module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 019. -/

theorem fin15Anchored_clause02432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02456 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02457 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02458 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02459 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02460 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02461 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02462 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02463 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02464 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02465 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02466 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02467 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02468 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02469 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02470 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02471 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02472 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02473 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02474 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02475 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02476 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02477 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02478 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02479 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02480 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02481 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02482 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02483 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02484 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02485 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02486 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02487 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02488 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02489 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02490 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02491 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02492 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02493 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02494 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02495 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02496 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02497 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02498 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02499 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02500 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02501 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02502 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02503 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02504 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02505 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02506 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02507 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02508 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02509 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02510 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02511 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02536 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02537 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02538 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02539 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02540 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02541 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02542 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02543 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02544 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02545 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02546 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02547 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02548 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02549 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02550 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02551 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02552 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02553 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02554 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02555 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02556 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02557 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02558 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02559 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
