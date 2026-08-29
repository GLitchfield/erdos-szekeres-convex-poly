module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 010. -/

theorem predecessorHalfFin13_clause03520 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0433 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03553 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03554 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03555 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03556 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03557 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03558 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03559 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03560 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03561 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03562 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03563 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03564 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03566 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03568 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03576 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0435 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03577 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03578 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03579 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03580 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03581 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03582 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03583 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03584 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03585 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03586 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03588 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03592 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0436 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03601 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03602 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03603 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03604 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03605 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03606 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03607 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03608 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03609 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03610 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03612 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03616 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03624 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0437 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03625 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03626 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03627 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03628 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03629 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03630 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03631 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03632 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03633 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03634 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03635 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03636 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03640 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03644 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03648 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0438 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03673 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03674 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03675 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03676 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03677 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03678 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03679 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03680 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03681 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03682 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03683 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03684 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03686 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03688 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0440 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03697 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03698 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03699 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03700 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03701 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03702 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03703 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03704 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03705 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03706 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03707 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03708 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03712 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0441 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03721 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03722 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03723 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03724 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03725 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03726 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03727 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03728 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03729 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03730 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03732 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03736 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0442 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03769 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03770 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
