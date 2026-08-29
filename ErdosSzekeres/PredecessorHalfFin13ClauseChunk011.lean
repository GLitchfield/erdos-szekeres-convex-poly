module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 011. -/

theorem predecessorHalfFin13_clause03771 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
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

theorem predecessorHalfFin13_clause03772 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
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

theorem predecessorHalfFin13_clause03773 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
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

theorem predecessorHalfFin13_clause03774 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
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

theorem predecessorHalfFin13_clause03775 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
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

theorem predecessorHalfFin13_clause03776 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi) := by
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

theorem predecessorHalfFin13_clause03777 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03778 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03779 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03780 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03782 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03784 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03788 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0224 PredecessorHalfFin13Atom0444 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03793 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03794 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03795 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03796 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03797 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03798 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03799 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03800 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03801 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03802 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03804 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03808 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03816 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0445 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03841 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03842 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03843 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03844 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03845 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03846 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03847 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03848 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03849 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03850 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03851 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03852 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03856 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03860 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0447 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03889 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03890 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03891 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03892 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03893 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03894 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03895 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03896 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03897 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03898 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03900 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03903 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03904 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03912 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0449 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03937 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03938 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03939 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03940 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03941 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03942 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03943 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03944 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03945 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03946 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03947 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03948 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03950 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03952 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03953 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03960 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0040 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0451 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03961 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03962 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03963 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03964 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03965 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03966 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03967 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03968 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03969 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03970 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03971 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03972 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03973 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03976 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03977 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03984 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0452 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03985 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03986 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03987 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03988 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03989 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03990 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03991 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03992 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03993 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03994 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03996 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04000 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04001 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04003 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04006 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04008 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0039 PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0453 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04009 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) := by
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

theorem predecessorHalfFin13_clause04010 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) := by
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

theorem predecessorHalfFin13_clause04011 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
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

theorem predecessorHalfFin13_clause04012 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) := by
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

theorem predecessorHalfFin13_clause04013 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
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

theorem predecessorHalfFin13_clause04014 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) := by
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

end ErdosSzekeres

end
