module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 001. -/

theorem fin15Anchored_clause00128 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00129 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00130 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00131 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00132 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00133 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00134 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00135 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00136 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00137 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00138 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00139 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00140 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00141 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00142 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00143 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00144 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00145 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00146 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00147 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00148 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00149 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00150 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00151 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
