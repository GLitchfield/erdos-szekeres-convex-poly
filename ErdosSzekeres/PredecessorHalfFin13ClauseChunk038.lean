module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 038. -/

theorem predecessorHalfFin13_clause13088 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13089 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13090 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13092 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13096 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13097 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13101 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13103 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13104 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0832 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13105 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13106 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13107 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13108 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13109 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13110 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13111 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13112 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13113 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13114 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13116 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13117 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13119 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13120 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13122 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13128 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0833 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13129 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13130 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13131 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13132 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13133 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13134 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13135 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13136 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13137 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13138 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13140 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13141 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13144 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0177 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0834 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13153 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13154 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13155 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13156 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13157 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13158 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13159 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13160 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13161 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13162 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13164 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13168 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13170 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13176 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0835 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13177 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13178 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13179 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13180 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13181 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13182 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13183 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13184 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13185 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13186 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13188 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13192 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0836 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13201 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13202 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13203 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13204 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13205 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13206 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13207 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13208 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13209 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13210 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13212 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13216 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13218 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0178 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0837 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13225 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13226 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13227 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13228 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13229 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13230 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13231 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13232 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13233 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13234 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13236 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13238 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13239 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13240 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13242 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0249 PredecessorHalfFin13Atom0838 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13249 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13250 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13251 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13252 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13253 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13254 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13255 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13256 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13257 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13258 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13260 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13263 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13264 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
