module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 012. -/

theorem predecessorHalfFin13_clause04015 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04016 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04017 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04018 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04019 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04020 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04024 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04025 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04029 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04031 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04032 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0454 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04057 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04058 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04059 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04060 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04061 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04062 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04063 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04064 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04065 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04066 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04067 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04068 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04070 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04072 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04073 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04076 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04077 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04079 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04080 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0051
    PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0456 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04081 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04082 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04083 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04084 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04085 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04086 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04087 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04088 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04089 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04090 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04092 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04096 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04097 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04101 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04103 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04104 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0457 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04105 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04106 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04107 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04108 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04109 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04110 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04111 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04112 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04113 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04114 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04115 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04116 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04120 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04128 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0458 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04129 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04130 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04131 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04132 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04133 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04134 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04135 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04136 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04137 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04138 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04140 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04144 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04147 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0459 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04177 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04178 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04179 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04180 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04181 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04182 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04183 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04184 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04185 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04186 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04188 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04190 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04192 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04196 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0461 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04201 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04202 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04203 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04204 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04205 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04206 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04207 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04208 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04209 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04210 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04212 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04216 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0462 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04225 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04226 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04227 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04228 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04229 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04230 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04231 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04232 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04233 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04234 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04236 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04240 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
