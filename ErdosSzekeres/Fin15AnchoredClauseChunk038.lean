module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 038. -/

theorem fin15Anchored_clause04864 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
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

theorem fin15Anchored_clause04865 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi) := by
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

theorem fin15Anchored_clause04866 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
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

theorem fin15Anchored_clause04867 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi) := by
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

theorem fin15Anchored_clause04868 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
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

theorem fin15Anchored_clause04869 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi) := by
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

theorem fin15Anchored_clause04870 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi) := by
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

theorem fin15Anchored_clause04871 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04872 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04873 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04874 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04875 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04876 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04877 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04878 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04879 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04880 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04881 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04882 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04883 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04884 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04885 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04886 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04887 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04888 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04889 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04890 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04891 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04892 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04893 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04894 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04895 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04896 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04897 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04898 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04899 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04900 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04901 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04902 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04903 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04904 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04905 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04906 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04907 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04908 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04909 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04910 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04911 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04944 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04945 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04946 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04947 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04948 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04949 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04950 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04951 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04952 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04953 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04954 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04955 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04956 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04957 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04958 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04959 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04960 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04961 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04962 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04963 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04964 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04965 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04966 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04967 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
