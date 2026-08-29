module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 033. -/

theorem predecessorHalfFin13_clause12217 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12218 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12219 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12220 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12221 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12222 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12223 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12224 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12225 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12226 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12228 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12230 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12231 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12232 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12233 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12236 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12237 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12239 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12240 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0179
    PredecessorHalfFin13Atom0207 PredecessorHalfFin13Atom0796 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12241 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12242 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12243 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12244 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12245 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12246 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12247 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12248 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12249 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12250 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12252 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12254 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12256 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12258 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12262 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12264 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0180
    PredecessorHalfFin13Atom0208 PredecessorHalfFin13Atom0797 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12265 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12266 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12267 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12268 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12269 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12270 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12271 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12272 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12273 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12274 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12276 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12280 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12288 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0174 PredecessorHalfFin13Atom0181
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0798 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12289 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12290 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12291 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12292 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12293 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12294 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12295 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12296 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12297 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12298 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12300 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12304 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12307 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12309 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12311 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12312 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0182
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0799 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12313 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12314 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12315 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12316 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12317 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12318 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12319 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12320 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12321 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12322 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12324 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12326 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12328 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12331 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12336 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0183
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0800 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12337 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12338 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12339 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12340 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12341 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12342 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12343 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12344 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12345 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12346 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12348 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12351 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12352 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12353 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0184
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0801 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12361 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12362 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12363 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12364 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12365 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12366 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12367 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12368 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12369 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12370 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12372 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12376 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12380 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0172 PredecessorHalfFin13Atom0185
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0802 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12385 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0186
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12386 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0186
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12387 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0186
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12388 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0186
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12389 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0173 PredecessorHalfFin13Atom0186
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
