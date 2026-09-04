module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 000. -/

theorem fin15Anchored_clause00000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00024 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00025 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00026 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00027 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00028 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00029 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00030 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00031 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00032 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00033 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00034 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00035 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00036 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00037 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00038 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00039 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00040 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00041 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00042 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00043 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00044 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00045 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00046 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00047 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00048 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00049 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00050 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00051 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00052 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00053 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00054 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00055 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00056 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00057 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00058 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00059 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00060 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00061 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00062 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00063 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00064 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00065 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00066 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00067 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00068 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00069 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00070 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00071 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 3) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00096 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00097 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00098 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00099 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00100 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00101 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00102 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00103 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00104 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00105 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00106 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00107 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00108 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00109 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00110 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00111 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00112 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00113 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00114 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00115 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00116 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00117 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00118 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00119 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00120 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00121 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00122 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00123 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00124 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
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

theorem fin15Anchored_clause00125 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
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

theorem fin15Anchored_clause00126 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
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

theorem fin15Anchored_clause00127 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
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

end ErdosSzekeres

end
