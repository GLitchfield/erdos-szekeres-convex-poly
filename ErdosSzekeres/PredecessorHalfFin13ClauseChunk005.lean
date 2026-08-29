module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 005. -/

theorem predecessorHalfFin13_clause02427 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02428 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02429 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02430 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02431 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02432 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02433 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02434 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02436 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02440 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02444 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02445 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02447 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02448 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0388 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02449 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02450 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02451 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02452 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02453 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02454 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02455 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02456 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02457 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02458 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02460 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02464 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02465 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02466 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02470 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02471 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02472 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0389 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02473 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02474 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02475 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02476 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02477 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02478 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02479 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02480 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02481 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02482 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02484 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02486 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02488 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02489 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02491 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02492 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02495 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02496 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0390 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02497 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02498 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02499 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02500 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02501 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02502 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02503 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02504 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02505 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02506 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02508 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02512 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02517 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02519 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02520 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0391 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02521 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02522 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02523 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02524 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02525 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02526 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02527 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02528 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02529 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02530 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02532 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02536 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02537 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02539 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02540 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02543 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02544 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0392 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02569 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02570 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02571 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02572 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02573 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02574 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02575 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02576 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02577 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02578 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02579 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02580 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02584 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02585 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02588 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02589 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02591 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02592 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0394 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02593 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02594 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02595 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02596 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02597 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02598 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02599 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02600 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02601 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02602 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02603 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02604 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02605 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02607 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02608 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02609 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02613 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02614 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02615 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02616 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0039
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0395 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02617 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0040
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02618 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0040
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02619 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0040
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
