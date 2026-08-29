module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 007. -/

theorem predecessorHalfFin13_clause02825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0404 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0404 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0404 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02831 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0404 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02832 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0404 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02833 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02834 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02835 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02836 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02837 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02838 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02839 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02840 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02841 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02842 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02843 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02844 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02848 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02851 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02852 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0405 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02881 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02882 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02883 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02884 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02885 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02886 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02887 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02888 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02889 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02890 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02891 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02892 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02896 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02897 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02900 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02901 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02903 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02904 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0407 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02905 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02906 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02907 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02908 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02909 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02910 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02911 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02912 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02913 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02914 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02916 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02920 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02924 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02928 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0188 PredecessorHalfFin13Atom0408 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02929 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02930 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02931 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02932 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02933 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02934 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02935 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02936 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02937 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02938 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02939 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02940 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02944 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02951 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02952 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0409 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02953 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02954 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02955 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02956 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02957 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02958 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02959 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02960 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02961 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02962 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02964 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02967 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02968 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02969 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02973 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02975 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02976 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0410 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03001 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03002 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03003 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03004 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03005 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03006 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03007 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03008 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03009 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03010 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03011 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03012 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03016 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03017 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03021 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03023 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03024 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0025 PredecessorHalfFin13Atom0030 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0412 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03025 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03026 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03027 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03028 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03029 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03030 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03031 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03032 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03033 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03034 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03036 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03039 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03040 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03048 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0027 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0413 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03049 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0026 PredecessorHalfFin13Atom0028 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0194 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
