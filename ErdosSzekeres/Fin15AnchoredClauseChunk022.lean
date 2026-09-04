module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 022. -/

theorem fin15Anchored_clause02816 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02817 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02818 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02819 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02820 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02821 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02822 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02823 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02824 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02825 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02826 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02827 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02828 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02829 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02830 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02831 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02832 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02833 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02834 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02835 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02836 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02837 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02838 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02839 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02840 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02841 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02842 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02843 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02844 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02845 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02846 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02847 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02848 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02849 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02850 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02851 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02852 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02853 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02854 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02855 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02856 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02857 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02858 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02859 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02860 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02861 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02862 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02863 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02864 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02865 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02866 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02867 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02868 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02869 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02870 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02871 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02872 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02873 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02874 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02875 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02876 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02877 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02878 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02879 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02880 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02881 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02882 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02883 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02884 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02885 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02886 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02887 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02888 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02889 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02890 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02891 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02892 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02893 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02894 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02895 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02896 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02897 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02898 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02899 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02900 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02901 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02902 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02903 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02904 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02905 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02906 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02907 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02908 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02909 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02910 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02911 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
