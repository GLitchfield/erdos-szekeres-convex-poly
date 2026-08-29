module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 009. -/

theorem predecessorHalfFin13_clause03318 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03319 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03320 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03321 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03322 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03323 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03324 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03328 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03330 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03334 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03336 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0041
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0425 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03337 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03338 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03339 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03340 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03341 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03342 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03343 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03344 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03345 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03346 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03348 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03352 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03353 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0042
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0426 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03361 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03362 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03363 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03364 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03365 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03366 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03367 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03368 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03369 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03370 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03372 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03376 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0043
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0427 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03409 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03410 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03411 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03412 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03413 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03414 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03415 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03416 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03417 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03418 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03419 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03420 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03424 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03428 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03432 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0031 PredecessorHalfFin13Atom0038 PredecessorHalfFin13Atom0045
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0429 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03433 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03434 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03435 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03436 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03437 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03438 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03439 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03440 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03441 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03442 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03443 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03444 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03448 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03456 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0033 PredecessorHalfFin13Atom0046
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0430 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03457 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03458 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03459 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03460 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03461 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03462 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03463 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03464 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03465 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03466 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03468 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03472 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03475 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0034 PredecessorHalfFin13Atom0047
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0431 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03481 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03482 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03483 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03484 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03485 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03486 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03487 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03488 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03489 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03490 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03492 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03496 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0035 PredecessorHalfFin13Atom0048
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0432 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03505 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03506 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03507 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03508 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03509 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03510 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03511 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03512 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0032 PredecessorHalfFin13Atom0036 PredecessorHalfFin13Atom0049
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause03513 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
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

theorem predecessorHalfFin13_clause03514 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
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

theorem predecessorHalfFin13_clause03515 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
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

theorem predecessorHalfFin13_clause03516 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
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

end ErdosSzekeres

end
