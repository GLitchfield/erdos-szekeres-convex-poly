module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 024. -/

theorem predecessorHalfFin13_clause10616 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0134 chi ∧
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

theorem predecessorHalfFin13_clause10617 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10618 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10619 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10620 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10624 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10632 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0729 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10633 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10634 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10635 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10636 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10637 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10638 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10639 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10640 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10641 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10642 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10643 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10646 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10647 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10648 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0730 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10657 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10658 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10659 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10660 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10661 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10662 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10663 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10664 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10665 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10666 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0731 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10681 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10682 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10683 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10684 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10685 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10686 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10687 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10688 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10689 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10690 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10692 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10696 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10697 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10703 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10704 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0732 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10705 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10706 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10707 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10708 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10709 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10710 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10711 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10712 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10713 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10715 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10716 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10720 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0733 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10729 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10730 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10731 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10732 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10733 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10734 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10735 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10736 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10737 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10738 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10740 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10744 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10752 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0734 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10753 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10754 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10755 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10756 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10757 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10758 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10759 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10760 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10761 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 PredecessorHalfFin13Atom0735 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10768 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 PredecessorHalfFin13Atom0735 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 PredecessorHalfFin13Atom0735 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 PredecessorHalfFin13Atom0735 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0230 PredecessorHalfFin13Atom0735 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10777 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10778 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10779 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10780 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10781 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10782 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10783 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10784 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10785 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10786 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10788 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10789 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10792 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10794 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0140 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0736 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10801 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0141 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10802 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0139 PredecessorHalfFin13Atom0141 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
