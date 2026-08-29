module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 001. -/

theorem predecessorHalfFin13_clause01519 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01520 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01521 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01522 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01524 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0030
    PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0350 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01537 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01538 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01539 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01540 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01541 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01542 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01543 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01544 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01545 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01547 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01551 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0351 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01561 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01562 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01563 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01564 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01565 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01566 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01567 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01568 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01569 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01571 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0352 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01585 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01586 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01587 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01588 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01589 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01590 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01591 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01592 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01593 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01595 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01603 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0033
    PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0353 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01609 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01610 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01611 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01612 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01613 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01614 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01615 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01616 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01617 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01618 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01619 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01620 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01624 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01632 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0034
    PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0354 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01633 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01634 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01635 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01636 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01637 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01638 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01639 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01640 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01641 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01642 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01648 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0035
    PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0355 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01657 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01658 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01659 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01660 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01661 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01662 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01663 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01664 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01665 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01666 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0036
    PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0356 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01705 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01706 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01707 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01708 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01709 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01710 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01711 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01712 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01713 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0358 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0358 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01716 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0358 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01720 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0358 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0038
    PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0358 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
