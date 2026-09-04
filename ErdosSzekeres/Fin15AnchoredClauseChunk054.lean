module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 054. -/

theorem fin15Anchored_clause06912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06944 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06945 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06946 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06947 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06948 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06949 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06950 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06951 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06952 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06953 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06954 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06955 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06956 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06957 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06958 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06959 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06960 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06961 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06962 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06963 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06964 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06965 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06966 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06967 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07024 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07025 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07026 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07027 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07028 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07029 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07030 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07031 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07032 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07033 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07034 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07035 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07036 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07037 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07038 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07039 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
