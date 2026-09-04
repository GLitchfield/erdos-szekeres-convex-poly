module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 007. -/

theorem fin15Anchored_clause00896 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00897 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00898 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00899 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00900 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00901 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00902 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00903 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00904 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00905 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00906 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00907 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00908 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00909 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00910 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00911 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00944 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00945 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00946 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00947 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00948 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00949 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00950 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00951 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00952 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00953 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00954 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00955 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00956 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00957 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00958 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00959 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00960 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00961 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00962 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00963 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00964 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00965 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00966 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00967 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause00999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
