module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 028. -/

theorem fin15Anchored_clause03584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03664 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03665 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03666 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03667 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03668 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03669 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03670 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03671 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03672 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03673 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03674 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03675 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03676 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03677 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03678 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03679 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03680 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03681 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03682 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03683 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03684 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03685 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03686 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03687 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03688 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03689 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03690 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03691 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03692 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03693 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03694 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03695 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03696 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03697 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03698 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03699 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03700 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03701 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03702 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03703 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03704 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03705 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03706 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03707 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03708 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03709 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03710 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03711 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
