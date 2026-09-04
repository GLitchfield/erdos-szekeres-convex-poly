module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 005. -/

theorem fin15Anchored_clause00640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00664 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00665 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00666 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00667 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00668 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00669 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00670 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00671 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00672 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00673 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00674 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00675 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00676 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00677 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00678 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00679 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00680 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00681 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00682 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00683 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00684 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00685 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00686 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00687 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00688 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00689 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00690 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00691 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00692 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00693 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00694 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00695 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00696 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00697 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00698 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00699 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00700 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00701 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00702 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00703 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00704 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00705 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00706 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00707 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00708 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00709 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00710 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00711 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00712 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00713 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00714 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00715 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00716 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00717 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00718 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00719 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00720 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00721 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00722 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00723 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00724 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00725 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00726 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00727 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00728 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00729 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00730 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00731 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00732 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00733 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00734 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00735 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00736 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00737 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00738 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00739 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00740 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00741 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00742 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00743 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00744 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00745 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00746 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00747 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00748 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00749 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00750 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00751 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00752 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00753 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00754 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00755 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00756 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00757 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00758 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00759 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
