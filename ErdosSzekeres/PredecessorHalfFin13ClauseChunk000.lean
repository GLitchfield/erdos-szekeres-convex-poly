module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 000. -/

theorem predecessorHalfFin13_clause01321 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01322 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01323 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01324 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01325 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01326 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01327 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01328 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01329 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01330 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01331 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01332 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01335 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01336 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01340 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0013 PredecessorHalfFin13Atom0022
    PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0342 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01345 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01346 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01347 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01348 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01349 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01350 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01351 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01352 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01353 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01354 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01355 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01356 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0014 PredecessorHalfFin13Atom0023
    PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0343 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01369 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01370 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01371 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01372 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01373 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01374 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01375 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01376 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01377 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01378 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01380 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01384 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01388 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0015 PredecessorHalfFin13Atom0024
    PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0344 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01393 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01394 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01395 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01396 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01397 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01398 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01399 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01400 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01401 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01402 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01403 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01404 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0025
    PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0345 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01417 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01418 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01419 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01420 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01421 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01422 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01423 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01424 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01425 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01426 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01427 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01428 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01432 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0026
    PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0346 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01441 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01442 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01443 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01444 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01445 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01446 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01447 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01448 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01449 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01450 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01452 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01456 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0027
    PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0347 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01465 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01466 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01467 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01468 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01469 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01470 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01471 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01472 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01473 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01483 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0012 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0028
    PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0348 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause01513 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) := by
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

theorem predecessorHalfFin13_clause01514 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) := by
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

theorem predecessorHalfFin13_clause01515 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
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

theorem predecessorHalfFin13_clause01516 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) := by
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

theorem predecessorHalfFin13_clause01517 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
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

theorem predecessorHalfFin13_clause01518 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) := by
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

end ErdosSzekeres

end
