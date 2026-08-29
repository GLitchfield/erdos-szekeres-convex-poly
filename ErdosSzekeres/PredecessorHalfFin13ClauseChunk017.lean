module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 017. -/

theorem predecessorHalfFin13_clause09362 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09363 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09364 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09365 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09366 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09367 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09368 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09369 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09370 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09372 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09376 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0677 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09385 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09386 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09387 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09388 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09389 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09390 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09391 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09392 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09393 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09394 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09396 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09400 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09401 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09408 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0137
    PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0678 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09409 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09410 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09411 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09412 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09413 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09414 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09415 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09416 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09417 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09418 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09420 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09424 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09432 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0138
    PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0679 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09433 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09434 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09435 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09436 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09437 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09438 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09439 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09440 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09441 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09442 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09444 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09445 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09446 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09448 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09456 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0139
    PredecessorHalfFin13Atom0175 PredecessorHalfFin13Atom0680 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09457 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09458 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09459 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09460 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09461 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09462 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09463 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09464 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09465 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09466 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09467 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09468 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09472 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0140
    PredecessorHalfFin13Atom0176 PredecessorHalfFin13Atom0681 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09481 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09482 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09483 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09484 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09485 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09486 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09487 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09488 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09489 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09490 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09491 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09492 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09494 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09495 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09496 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0141
    PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0682 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09505 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09506 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09507 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09508 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09509 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09510 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09511 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09512 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09513 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09514 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09516 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09520 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0142
    PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0683 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09529 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09530 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09531 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09532 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09533 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09534 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09535 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09536 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0179 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0143
    PredecessorHalfFin13Atom0179 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09537 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
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

end ErdosSzekeres

end
