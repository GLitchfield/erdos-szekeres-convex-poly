module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 019. -/

theorem predecessorHalfFin13_clause09723 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
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

theorem predecessorHalfFin13_clause09724 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
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

theorem predecessorHalfFin13_clause09725 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
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

theorem predecessorHalfFin13_clause09726 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
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

theorem predecessorHalfFin13_clause09727 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
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

theorem predecessorHalfFin13_clause09728 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
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

theorem predecessorHalfFin13_clause09729 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09730 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09731 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09732 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09736 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09740 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0692 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09745 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09746 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09747 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09748 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09749 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09750 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09751 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09752 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09753 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09754 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09756 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09760 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09763 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09768 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0693 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09769 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09770 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09771 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09772 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09773 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09774 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09775 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09776 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09777 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09778 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09780 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09783 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09784 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0694 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09793 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09794 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09795 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09796 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09797 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09798 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09799 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09800 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09801 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09802 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09804 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09807 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09808 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09812 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09816 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0695 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09817 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09818 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09819 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09820 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09821 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09822 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09823 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09824 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09825 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09826 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09828 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09832 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09833 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09840 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0696 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09841 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09842 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09843 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09844 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09845 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09846 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09847 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09848 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09849 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09850 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09852 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09856 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0697 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09865 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09866 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09867 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09868 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09869 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09870 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09871 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09872 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09873 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09874 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09875 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09876 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09877 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09880 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09884 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09887 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09888 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0698 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09889 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09890 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09891 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09892 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09893 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09894 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09895 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09896 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09897 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
