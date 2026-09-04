module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 040. -/

theorem fin15Anchored_clause05120 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
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

theorem fin15Anchored_clause05121 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05122 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05123 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05124 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05125 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05126 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05127 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05128 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05129 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05130 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05131 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05132 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05133 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05134 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05135 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05136 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05137 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05138 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05139 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05140 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05141 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05142 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05143 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05144 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05145 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05146 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05147 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05148 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05149 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05150 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05151 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
