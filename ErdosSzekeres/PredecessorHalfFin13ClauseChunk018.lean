module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 018. -/

theorem predecessorHalfFin13_clause09538 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09540 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09544 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09545 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09548 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09552 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0684 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09553 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09554 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09555 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09556 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09557 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09558 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09559 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09560 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09561 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09562 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09564 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09568 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09576 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0144
    PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0685 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09577 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09578 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09579 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09580 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09581 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09582 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09583 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09584 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09585 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09586 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09588 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09592 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0686 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09601 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09602 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09603 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09604 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09605 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09606 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09607 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09608 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09609 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09610 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09612 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09615 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09616 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09618 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09624 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0687 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09625 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09626 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09627 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09628 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09629 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09630 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09631 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09632 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09633 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09634 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09636 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09640 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09642 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09646 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09648 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0688 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09649 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09650 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09651 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09652 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09653 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09654 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09655 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09656 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09657 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09658 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09660 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09664 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09672 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0689 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09673 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09674 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09675 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09676 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09677 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09678 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09679 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09680 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09681 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09682 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09683 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09684 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09688 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09692 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0690 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09697 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09698 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09699 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09700 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09701 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09702 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09703 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09704 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09705 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09706 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09708 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09712 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0691 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09721 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09722 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
