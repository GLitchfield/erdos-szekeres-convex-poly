module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 010. -/

theorem fin15Anchored_clause01280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
