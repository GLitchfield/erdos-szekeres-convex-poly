module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 023. -/

theorem predecessorHalfFin13_clause10443 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10444 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10445 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10446 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10447 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10448 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10449 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10450 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10452 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10455 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10456 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10460 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0153
    PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0722 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10465 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10466 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10467 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10468 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10469 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10470 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10471 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10472 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10473 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10475 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10478 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10486 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0154
    PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0723 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10489 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10490 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10491 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10492 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10493 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10494 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10495 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10496 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10497 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10500 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0155
    PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0724 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10513 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10514 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10515 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10516 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10517 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10518 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10519 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10520 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10521 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10522 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10524 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0156
    PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0725 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10537 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10538 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10539 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10540 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10541 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10542 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10543 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10544 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10545 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10547 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10551 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10556 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0157
    PredecessorHalfFin13Atom0221 PredecessorHalfFin13Atom0726 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10561 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10562 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10563 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10564 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10565 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10566 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10567 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10568 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10569 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10582 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0222 PredecessorHalfFin13Atom0727 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10585 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10586 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10587 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10588 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10589 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10590 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10591 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10592 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10593 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0223 PredecessorHalfFin13Atom0728 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10609 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10610 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10611 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10612 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10613 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10614 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10615 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
