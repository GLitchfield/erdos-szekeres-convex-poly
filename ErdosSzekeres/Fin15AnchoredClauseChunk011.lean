module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 011. -/

theorem fin15Anchored_clause01408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
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

theorem fin15Anchored_clause01409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
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

theorem fin15Anchored_clause01410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01456 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01457 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01458 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01459 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01460 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01461 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01462 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01463 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01464 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01465 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01466 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01467 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01468 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01469 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01470 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01471 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01472 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01473 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01474 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0132 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01475 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0132 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01476 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0132 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0367 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01477 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01478 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01479 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01480 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01481 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01482 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01483 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01484 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01485 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01486 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01487 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01488 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01489 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01490 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01491 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01492 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01493 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01494 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01495 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01496 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01497 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01498 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01499 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01500 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01501 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01502 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01503 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01504 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01505 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01506 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01507 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01508 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01509 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01510 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01511 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01512 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01513 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01514 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01515 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01516 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01517 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01518 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01519 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01520 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01521 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01522 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01523 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01524 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01525 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01526 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01527 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01528 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01529 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01530 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01531 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01532 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01533 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01534 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01535 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
