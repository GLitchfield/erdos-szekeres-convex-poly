module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 004. -/

theorem predecessorHalfFin13_clause02152 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0016 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0376 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02161 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02162 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02163 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02164 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02165 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02166 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02167 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02168 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02169 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02170 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02172 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02176 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02183 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02184 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0377 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02185 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02186 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02187 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02188 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02189 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02190 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02191 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02192 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02193 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02194 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02196 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02199 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02200 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02204 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02207 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02208 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0378 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02233 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02234 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02235 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02236 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02237 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02238 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02239 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02240 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02241 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02242 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02244 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02248 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02249 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02252 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02253 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02256 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0017 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0380 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02257 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02258 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02259 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02260 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02261 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02262 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02263 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02264 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02265 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02266 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02267 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02268 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02272 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02273 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02277 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02280 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0381 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02305 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02306 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02307 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02308 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02309 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02310 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02311 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02312 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02313 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02314 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02315 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02316 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02320 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02321 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02324 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02325 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02327 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02328 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0018 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0383 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02353 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02354 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02355 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02356 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02357 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02358 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02359 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02360 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02361 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02362 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02363 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02364 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02368 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02369 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02373 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02376 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0019 PredecessorHalfFin13Atom0021 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0385 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02401 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02402 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02403 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02404 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02405 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02406 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02407 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02408 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02409 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02410 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02412 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02416 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02424 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0023 PredecessorHalfFin13Atom0031
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0387 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02425 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause02426 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0022 PredecessorHalfFin13Atom0024 PredecessorHalfFin13Atom0032
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
