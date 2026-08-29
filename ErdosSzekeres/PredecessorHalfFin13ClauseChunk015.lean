module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 015. -/

theorem predecessorHalfFin13_clause04809 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04810 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04812 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04814 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04816 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0487 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04825 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04826 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04827 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04828 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04829 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04830 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04831 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04832 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04833 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04834 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04835 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04836 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04838 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04840 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04848 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0488 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04873 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04874 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04875 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04876 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04877 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04878 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04879 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04880 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04881 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04882 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04884 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04886 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04888 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04892 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04896 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0490 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04897 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04898 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04899 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04900 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04901 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04902 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04903 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04904 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04905 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04906 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04908 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04910 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04912 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04913 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04920 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0491 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04945 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04946 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04947 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04948 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04949 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04950 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04951 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04952 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04953 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04954 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04956 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04958 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04960 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04967 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04968 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0493 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04993 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04994 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04995 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04996 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04997 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04998 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04999 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05000 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05001 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05002 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05004 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05008 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05013 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05016 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0054 PredecessorHalfFin13Atom0056 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0495 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05041 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05042 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05043 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05044 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05045 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05046 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05047 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05048 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05049 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05050 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05052 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05054 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05056 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05063 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05064 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0497 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05089 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05090 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05091 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05092 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05093 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05094 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05095 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05096 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05097 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05098 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05100 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05102 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05104 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05106 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
